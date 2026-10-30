"""Search rules of PLDI'16 §3.7, beyond isolated pruning examples."""

from time import monotonic
import pytest
from aeon.compilation.session import CompilationSession


from aeon.core.terms import Annotation, If, Var, TypeAbstraction, Rec
from aeon.core.types import t_int
from aeon.synthesis.modules.synquid.engine import synthes_memory
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from tests.synquid_round_trip_test import name, parse_type
from tests.driver import check_and_return_core
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.core.types import top
from aeon.core.substitutions import substitution


@pytest.fixture(autouse=True)
def compilation_session():
    with CompilationSession().activate():
        yield


def search(ctx, goal, *, depth=0, matches=0, names=None, seconds=15):
    mem = {"synquid_deadline": monotonic() + seconds, "synquid_match_depth": matches}
    terms = synthes_memory(ctx, depth, goal, lambda n: names is not None and n.name not in names, mem)
    for term in terms:
        if check_type(ctx, term, goal):
            return term, mem
    raise AssertionError("No verified solution")


def test_conditionals_do_not_consume_application_depth():
    ctx = built_std_context().with_var(name("x"), t_int).with_var(name("y"), t_int).with_var(name("z"), t_int)
    # Bind z explicitly (the shared parser helper only binds x/y).
    from aeon.core.bind import bind_type
    from aeon.core.parser import parse_type as raw
    from aeon.core.liquid_ops import ops

    goal = bind_type(
        raw("{v:Int | (((v >= x) && (v >= y)) && (v >= z)) && (((v == x) || (v == y)) || (v == z))}"),
        [(n.name, n) for n in ops] + [(s, name(s)) for s in ("Int", "x", "y", "z")],
    )
    term, mem = search(ctx, goal, depth=0, names={"x", "y", "z"})
    assert isinstance(term, Annotation) and isinstance(term.expr, If)
    assert mem["synquid_stats"].abduced_guards >= 2


def test_tabs_constructs_a_polymorphic_identity():
    goal = parse_type("forall a:B, (x:a) -> a")
    term, _ = search(built_std_context(), goal, names={"x"})
    assert isinstance(term, TypeAbstraction)


def test_match_uses_constructor_facts_at_separate_depth():
    source = """
    inductive Flag
    | off : {v:Flag | tag v = 0}
    | on : {v:Flag | tag v = 1}
    + tag (v:Flag) : Int
    def code (f:Flag) : {v:Int | v = tag f} := ?hole;
    """
    program, ctx, _, _ = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, program)
    hole = targets[0][1][0]
    goal, local = get_holes_info(ctx, program, top, targets, refined_types=True)[hole]
    term, mem = search(local, goal, depth=0, matches=1, names={"f"})
    assert mem["synquid_stats"].matches >= 1
    assert mem["synquid_stats"].match_abductions >= 1
    assert check_type(ctx, substitution(program, term, hole), top)


def test_incremental_unification_retains_related_free_variables():
    from aeon.synthesis.modules.synquid.constraints import ConstraintState
    from aeon.synthesis.modules.synquid.solver import Status
    from aeon.typechecking.context import TypeConstructorBinder
    from aeon.core.types import TypeConstructor

    ctx = built_std_context()
    ctx.entries.append(TypeConstructorBinder(name("Seq"), [name("a")]))
    state = ConstraintState(ctx)
    alpha, beta = state.fresh_variable(), state.fresh_variable()
    state.subtype(alpha, TypeConstructor(name("Seq"), [beta]))
    assert state.solve() == Status.VALID
    assert state.unresolved(state.resolve(alpha))
    sibling = state.fork()
    state.subtype(parse_type("{v:Int | v >= 0}"), beta)
    assert state.solve() == Status.VALID
    assert not state.unresolved(alpha)
    assert sibling.unresolved(alpha)
    # Recursive shape equations fail the occurs check instead of looping.
    sibling.subtype(beta, TypeConstructor(name("Seq"), [beta]))
    assert sibling.solve() == Status.INVALID


def test_unanchored_argument_shape_can_come_from_a_nested_application():
    from aeon.core.types import TypeConstructor, AbstractionType
    from aeon.typechecking.context import TypeConstructorBinder

    ctx = built_std_context()
    box = TypeConstructor(name("Box"))
    ctx.entries.append(TypeConstructorBinder(name("Box"), []))
    ctx = ctx.with_var(name("box"), AbstractionType(name("n"), t_int, box))
    ctx = ctx.with_var(name("consume"), parse_type("forall a:B, (x:a) -> Int"))
    terms = synthes_memory(ctx, 2, t_int, lambda n: n.name not in {"box", "consume"}, {}, conditionals=False)
    assert any("consume" in str(t) and "box" in str(t) and check_type(ctx, t, t_int) for t in terms)


def test_fix_synthesizes_a_decreasing_recursive_function():
    source = """
    inductive Nat
    | zero : {v:Nat | size v = 0}
    | succ (p:{v:Nat | size v >= 0}) : {v:Nat | size v = size p + 1}
    + size (v:Nat) : Int
    def dec (x:Int) : {v:Int | v = x - 1} := x - 1;
    def build : (n:{v:Int | v >= 0}) -> {v:Nat | size v = n} := ?hole;
    """
    program, root, _, _ = check_and_return_core(source)
    targets = incomplete_functions_and_holes(root, program)
    hole = targets[0][1][0]
    goal, local = get_holes_info(root, program, top, targets, refined_types=True)[hole]
    # The generated recursive name and parameter are introduced by the rules.
    term, mem = search(local, goal, depth=3, names={"Nat_zero", "Nat_succ", "dec", "n"}, seconds=30)
    assert isinstance(term, Rec)
    assert mem["synquid_stats"].recursive_functions >= 1
    assert check_type(root, substitution(program, term, hole), top)


def test_non_executable_guard_is_synthesized_from_its_refinement():
    from aeon.core.liquid import LiquidApp, LiquidVar, LiquidLiteralInt
    from aeon.core.types import AbstractionType, RefinedType, t_bool
    from aeon.typechecking.context import UninterpretedBinder
    from tests.synquid_round_trip_test import liq

    ctx = built_std_context().with_var(name("x"), t_int)
    predicate = name("p")
    ctx.entries.append(UninterpretedBinder(predicate, AbstractionType(name("n"), t_int, t_bool)))
    b, v, x = (LiquidVar(name(n)) for n in ("b", "v", "x"))
    condition = LiquidApp(predicate, [x])
    decision = AbstractionType(
        name("arg"), t_int, RefinedType(name("b"), t_bool, liq("==", b, LiquidApp(predicate, [LiquidVar(name("arg"))])))
    )
    ctx = ctx.with_var(name("decide"), decision)
    goal = RefinedType(
        name("v"),
        t_int,
        liq(
            "||",
            liq("&&", condition, liq("==", v, LiquidLiteralInt(0))),
            liq("&&", liq("!", condition), liq("==", v, LiquidLiteralInt(1))),
        ),
    )
    term, _ = search(ctx, goal, depth=1, names={"x", "decide"})
    assert isinstance(term, Annotation) and isinstance(term.expr, If)
    assert "decide" in str(term.expr.cond)


def test_match_can_scrutinize_an_application():
    source = """
    inductive Flag
    | off : {v:Flag | tag v = 0}
    | on : {v:Flag | tag v = 1}
    + tag (v:Flag) : Int
    def observe (n:Int) : Flag := if n = 0 then Flag.off else Flag.on;
    def code (x:Int) : {v:Int | v = tag (observe x)} := ?hole;
    """
    program, ctx, _, _ = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, program)
    hole = targets[0][1][0]
    goal, local = get_holes_info(ctx, program, top, targets, refined_types=True)[hole]
    term, mem = search(local, goal, depth=1, matches=1, names={"x", "observe"})
    from aeon.core.terms import Let

    assert isinstance(term, Let)
    assert mem["synquid_stats"].matches >= 1
    assert check_type(ctx, substitution(program, term, hole), top)


def test_recursive_hypothesis_uses_lexicographic_order():
    from aeon.synthesis.modules.synquid.functions import weaken
    from aeon.core.terms import Application, Literal

    schema = parse_type("(x:{v:Int | v >= 0}) -> (y:{v:Int | v >= 0}) -> Int")
    x, y = schema.var_name, schema.type.var_name
    weakened = weaken(schema, [(0, Var(x)), (1, Var(y))])
    ctx = built_std_context().with_var(x, parse_type("{v:Int | v == 1}")).with_var(y, parse_type("{v:Int | v == 1}"))
    ctx = ctx.with_var(name("f"), weakened)

    def call(a, b):
        return Application(Application(Var(name("f")), Literal(a, t_int)), Literal(b, t_int))

    assert check_type(ctx, call(0, 100), t_int)
    assert check_type(ctx, call(1, 0), t_int)
    assert not check_type(ctx, call(1, 1), t_int)
    assert not check_type(ctx, call(2, 0), t_int)
    assert not check_type(ctx, call(0, -1), t_int)


def test_unconstrained_phantom_type_is_closed_at_a_complete_application():
    ctx = built_std_context().with_var(name("constant"), parse_type("forall a:B, (x:Int) -> {v:Int | v == 7}"))
    terms = synthes_memory(
        ctx, 1, parse_type("{v:Int | v == 7}"), lambda n: n.name != "constant", {}, conditionals=False
    )
    term = next(t for t in terms if "constant" in str(t) and check_type(ctx, t, parse_type("{v:Int | v == 7}")))
    assert "_sq_type" not in str(term)


def test_polymorphic_surface_hole_uses_tabs_and_match():
    from aeon.synthesis.entrypoint import synthesize_holes
    from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
    from aeon.synthesis.uis.api import SilentSynthesisUI

    source = """
    inductive Option a
    | none : {v:(Option a) | tag v = 0}
    | some (x:a) : {v:(Option a) | tag v = 1}
    + tag (v:(Option a)) : Int
    def code (o:(Option a)) : {v:Int | v = tag o} := ?hole;
    """
    program, ctx, ectx, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, program)
    function, (hole,) = targets[0]
    metadata.setdefault(function, {})["synquid_max_level"] = 0
    backend = SynquidSynthesizer()
    mapping = synthesize_holes(ctx, ectx, program, targets, metadata, backend, budget=10, ui=SilentSynthesisUI())
    assert backend.stats.matches >= 1
    assert check_type(ctx, substitution(program, mapping[hole], hole), top)


def test_outer_refinement_is_solved_before_nested_shape_is_known():
    from aeon.core.types import TypeConstructor, TypeVar, RefinedType, AbstractionType
    from aeon.core.liquid import LiquidVar, LiquidLiteralInt, LiquidLiteralBool
    from aeon.typechecking.context import TypeConstructorBinder, UninterpretedBinder
    from aeon.synthesis.modules.synquid.constraints import ConstraintState
    from aeon.synthesis.modules.synquid.solver import Status
    from tests.synquid_round_trip_test import liq

    seq = name("Seq")
    ctx = built_std_context()
    ctx.entries.append(TypeConstructorBinder(seq, [name("a")]))
    ctx.entries.append(
        UninterpretedBinder(
            name("length"), AbstractionType(name("s"), TypeConstructor(seq, [TypeVar(name("a"))]), t_int)
        )
    )
    state = ConstraintState(ctx)
    alpha, beta = state.fresh_variable(), state.fresh_variable()
    goal = RefinedType(
        name("v"), TypeConstructor(seq, [beta]), liq(">", liq("length", LiquidVar(name("v"))), LiquidLiteralInt(0))
    )
    state.subtype(alpha, goal)
    assert state.solve() == Status.VALID
    actual = state.materialize(alpha)
    assert isinstance(actual, RefinedType)
    assert actual.refinement != LiquidLiteralBool(True)
    assert state.unresolved(actual)
    state.subtype(t_int, beta)
    assert state.solve() == Status.VALID
    assert not state.unresolved(alpha)


def test_polymorphic_nullary_components_have_zero_application_depth():
    from aeon.core.types import TypeConstructor, TypePolymorphism, TypeVar, Kind
    from aeon.typechecking.context import TypeConstructorBinder
    from aeon.core.terms import TypeApplication

    ctx = built_std_context()
    box, a = name("Box"), name("a")
    ctx.entries.append(TypeConstructorBinder(box, [a]))
    ctx = ctx.with_var(name("empty"), TypePolymorphism(a, Kind.BASE, TypeConstructor(box, [TypeVar(a)])))
    term, mem = search(ctx, TypeConstructor(box, [t_int]), names={"empty"})
    assert isinstance(term, TypeApplication)
    assert mem["synquid_stats"].argument_candidates == 0


def test_fix_and_tabs_synthesize_polymorphic_replication():
    source = """
    inductive Chain a
    | empty : {v:(Chain a) | size v = 0}
    | link (h:a) (t:{v:(Chain a) | size v >= 0}) : {v:(Chain a) | size v = size t + 1}
    + size (v:(Chain a)) : Int
    def dec (x:Int) : {v:Int | v = x - 1} := x - 1;
    def repeat : (n:{v:Int | v >= 0}) -> (x:a) -> {v:(Chain a) | size v = n} := ?hole;
    """
    program, ctx, _, _ = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, program)
    hole = targets[0][1][0]
    goal, local = get_holes_info(ctx, program, top, targets, refined_types=True)[hole]
    term, mem = search(local, goal, depth=3, names={"Chain_empty", "Chain_link", "dec", "n", "x"}, seconds=30)
    assert isinstance(term, Rec)
    assert mem["synquid_stats"].recursive_functions >= 1
    assert check_type(ctx, substitution(program, term, hole), top)


def test_unanchored_nested_application_infers_higher_order_arguments():
    from aeon.core.types import TypeConstructor
    from aeon.typechecking.context import TypeConstructorBinder

    ctx = built_std_context()
    ctx.entries.append(TypeConstructorBinder(name("Seq"), [name("a")]))
    ctx = ctx.with_var(name("xs"), TypeConstructor(name("Seq"), [t_int]))
    ctx = ctx.with_var(name("inc"), parse_type("(n:Int) -> Int"))
    ctx = ctx.with_var(name("map"), parse_type("forall a:B, forall b:B, (f:(n:a) -> b) -> (xs:Seq a) -> Seq b"))
    ctx = ctx.with_var(name("consume"), parse_type("forall a:B, (x:a) -> Int"))
    terms = synthes_memory(
        ctx,
        2,
        t_int,
        lambda n: n.name not in {"xs", "inc", "map", "consume"},
        {"synquid_deadline": monotonic() + 15},
        conditionals=False,
    )
    assert any("consume" in str(t) and "map" in str(t) and "inc" in str(t) and check_type(ctx, t, t_int) for t in terms)
