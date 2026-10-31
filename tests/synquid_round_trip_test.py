"""Application-local pruning and isolated, persistent refinement obligations."""

from itertools import product


from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.parser import parse_type as parse_raw_type
from aeon.core.bind import bind_type
from aeon.core.liquid_ops import ops
from aeon.core.terms import Application, Literal, Var
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    Kind,
    RefinementPolymorphism,
    t_int,
    t_bool,
)
from aeon.synthesis.modules.synquid.constraints import ConstraintState
from aeon.synthesis.modules.synquid.engine import _application_terms, synthes_memory
from aeon.synthesis.modules.synquid.round_trip import ApplicationState
from aeon.synthesis.modules.synquid.solver import Status
from aeon.typechecking.context import TypeConstructorBinder, UninterpretedBinder
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name
from aeon.utils.ctx_helpers import built_std_context


def name(s):
    return Name(s, 0)


def parse_type(source):
    names = ["Int", "Bool", "Float", "Seq", "x", "y"]
    return bind_type(parse_raw_type(source), [(n, name(n)) for n in names] + [(n.name, n) for n in ops])


def liq(op, *args):
    return LiquidApp(name(op), list(args))


def append_fixture(prefix=6):
    list_t = TypeConstructor(name("Seq"))
    ctx = built_std_context()
    ctx.entries.extend(
        [
            TypeConstructorBinder(name("Seq"), []),
            UninterpretedBinder(name("len"), AbstractionType(name("s"), list_t, t_int)),
        ]
    )
    v, x, y = (LiquidVar(name(n)) for n in ("v", "xs", "ys"))

    def length(t):
        return liq("len", t)

    nat = RefinedType(name("v"), list_t, liq(">=", length(v), LiquidLiteralInt(0)))
    result = RefinedType(name("v"), list_t, liq("==", length(v), liq("+", length(x), length(y))))
    fn = AbstractionType(name("xs"), nat, AbstractionType(name("ys"), nat, result))
    ctx = ctx.with_var(name("append"), fn)
    for n, size in (("prefix", prefix), ("suffix", 2)):
        ctx = ctx.with_var(name(n), RefinedType(name("v"), list_t, liq("==", length(v), LiquidLiteralInt(size))))
    goal = RefinedType(name("v"), list_t, liq("==", length(v), LiquidLiteralInt(5)))
    return ctx, fn, goal


def test_measure_rejects_prefix_before_second_generator(monkeypatch):
    ctx, fn, goal = append_fixture()
    state = ConstraintState(ctx)
    calls = []

    def arguments(ctx, level, goal, skip, mem, state):
        calls.append(goal)
        yield Var(name("prefix"))

    monkeypatch.setattr("aeon.synthesis.modules.synquid.engine._arg_gen", arguments)
    terms = list(
        _application_terms(ctx, 1, Var(name("append")), ApplicationState.start(state, fn, goal), lambda _: False, {})
    )
    assert terms == []
    assert len(calls) == 1
    assert state.stats.argument_candidates == 1
    assert state.stats.partial_rejections == 1
    assert state.stats.full_validations == 0


def test_measure_obligation_is_pending_then_discharged_and_backtracking_isolated():
    ctx, fn, goal = append_fixture(prefix=3)
    start = ApplicationState.start(ConstraintState(ctx), fn, goal)
    assert start.check() == Status.VALID
    assert start.state.pending
    good = start.choose(Var(name("prefix")))
    assert good.check() == Status.VALID
    complete = good.choose(Var(name("suffix")))
    assert complete.check() == Status.VALID
    assert not complete.state.pending
    bad = good.choose(Var(name("prefix")))
    assert bad.check() == Status.INVALID
    assert good.choose(Var(name("suffix"))).check() == Status.VALID
    assert start.state.pending


def test_pruning_preserves_all_solutions_in_finite_component_grammar(monkeypatch):
    ctx, fn, goal = append_fixture(prefix=3)
    leaves = [Var(name("prefix")), Var(name("suffix"))]
    monkeypatch.setattr("aeon.synthesis.modules.synquid.engine._arg_gen", lambda *args: iter(leaves))
    exhaustive = [Application(Application(Var(name("append")), x), y) for x, y in product(leaves, repeat=2)]
    valid = {repr(t) for t in exhaustive if check_type(ctx, t, goal)}
    generated = list(
        _application_terms(
            ctx, 1, Var(name("append")), ApplicationState.start(ConstraintState(ctx), fn, goal), lambda _: False, {}
        )
    )
    assert valid
    assert {repr(t) for t in generated if check_type(ctx, t, goal)} == valid


def test_dependent_argument_goal_preserved():
    fn = parse_type("(x:Int) -> (y:{v:Int | v > x}) -> Int")
    start = ApplicationState.start(ConstraintState(built_std_context()), fn, t_int)
    chosen = start.choose(Literal(3, t_int))
    assert "3" in repr(chosen.params[0][1])
    assert chosen.choose(Literal(4, t_int)).check() == Status.VALID
    assert chosen.choose(Literal(2, t_int)).check() == Status.INVALID


def test_polymorphic_element_refinement_rejected_before_suffix(monkeypatch):
    ctx = built_std_context()
    ctx.entries.append(TypeConstructorBinder(name("Seq"), [name("a")]))
    pos, nat = parse_type("{v:Int | v > 0}"), parse_type("{v:Int | v >= 0}")

    def seq(element):
        return TypeConstructor(name("Seq"), [element])

    fn = parse_type("forall a:B, (xs:Seq a) -> (ys:Seq a) -> Seq a")
    ctx = ctx.with_var(name("append"), fn).with_var(name("xs"), seq(nat))
    state = ConstraintState(ctx)
    calls = []

    def arguments(*args):
        calls.append(args[2])
        yield Var(name("xs"))

    monkeypatch.setattr("aeon.synthesis.modules.synquid.engine._arg_gen", arguments)
    terms = list(
        synthes_memory(ctx, 1, seq(pos), lambda n: n.name not in ("append", "xs"), {}, state, conditionals=False)
    )
    assert not terms
    assert len(calls) == 1
    assert state.stats.partial_rejections == 1


def test_constraint_states_do_not_share_memoized_candidates():
    ctx = built_std_context().with_var(name("x"), t_int)
    goal = parse_type("{v:Int | v > 0}")
    positive = ConstraintState(ctx).assume(liq(">", LiquidVar(name("x")), LiquidLiteralInt(0)))
    negative = ConstraintState(ctx).assume(liq("<=", LiquidVar(name("x")), LiquidLiteralInt(0)))
    mem = {}
    assert Var(name("x")) in list(synthes_memory(ctx, 0, goal, lambda _: False, mem, positive))
    assert Var(name("x")) not in list(synthes_memory(ctx, 0, goal, lambda _: False, mem, negative))


def test_refined_polymorphic_instantiation_survives_final_verification():
    ctx = built_std_context()
    fn = parse_type("forall a:B, (x:a) -> a")
    goal = parse_type("{v:Int | v > 0}")
    ctx = ctx.with_var(name("identity"), fn).with_var(name("positive"), goal)
    terms = list(synthes_memory(ctx, 1, goal, lambda n: n.name not in ("identity", "positive"), {}, conditionals=False))
    assert terms
    assert any(check_type(ctx, term, goal) for term in terms)
    # The type application itself carries the solved refinement, rather than
    # asking final verification to recover a discarded instantiation.
    assert any(isinstance(t, Application) and isinstance(t.fun.type, RefinedType) for t in terms)


def test_type_shape_discovered_from_argument_and_higher_order_argument_delayed():
    ctx = built_std_context()
    fn = parse_type("forall a:B, (f:(z:a) -> Int) -> (x:a) -> Int")
    # a is absent from the result, and the first (higher-order) argument needs
    # its shape. Choosing the String argument first determines f's domain.
    string = TypeConstructor(name("String"))
    convert = AbstractionType(name("s"), string, t_int)
    ctx = ctx.with_var(name("apply"), fn).with_var(name("text"), string).with_var(name("length"), convert)

    def skip(n):
        return n.name not in ("apply", "text", "length")

    terms = list(synthes_memory(ctx, 1, t_int, skip, {}, conditionals=False))
    assert any("apply" in str(t) and "text" in str(t) and check_type(ctx, t, t_int) for t in terms)


def test_refined_instantiation_uses_all_result_occurrences():
    ctx = built_std_context()
    ctx.entries.append(TypeConstructorBinder(name("Seq"), [name("a"), name("b")]))
    alpha = name("a")
    fn = TypePolymorphism(
        alpha,
        Kind.BASE,
        AbstractionType(name("x"), TypeVar(alpha), TypeConstructor(name("Seq"), [TypeVar(alpha), TypeVar(alpha)])),
    )
    positive, natural = parse_type("{v:Int | v > 0}"), parse_type("{v:Int | v >= 0}")
    goal = TypeConstructor(name("Seq"), [natural, positive])
    ctx = ctx.with_var(name("pair"), fn).with_var(name("positive"), positive)
    terms = list(synthes_memory(ctx, 1, goal, lambda n: n.name not in ("pair", "positive"), {}, conditionals=False))
    assert terms
    assert any(check_type(ctx, t, goal) for t in terms)


def test_abstract_refinement_component_is_preserved_and_verified():
    ctx = built_std_context()
    refined = RefinedType(name("v"), t_int, liq("p", LiquidVar(name("v"))))
    fn = RefinementPolymorphism(
        name("p"), AbstractionType(name("v"), t_int, t_bool), AbstractionType(name("x"), refined, refined)
    )
    goal = parse_type("{v:Int | v > 0}")
    ctx = ctx.with_var(name("wrap"), fn).with_var(name("positive"), goal)
    terms = list(synthes_memory(ctx, 1, goal, lambda n: n.name not in ("wrap", "positive"), {}, conditionals=False))
    assert terms
    assert any(check_type(ctx, term, goal) for term in terms)


def test_polymorphic_abstract_refinement_with_solved_liquid_type_argument():
    alpha = TypeVar(name("a"))
    refined = RefinedType(name("v"), alpha, liq("p", LiquidVar(name("v"))))
    fn = TypePolymorphism(
        alpha.name,
        Kind.BASE,
        RefinementPolymorphism(
            name("p"), AbstractionType(name("v"), alpha, t_bool), AbstractionType(name("x"), refined, refined)
        ),
    )
    goal = parse_type("{v:Int | v > 0}")
    ctx = built_std_context().with_var(name("wrap"), fn).with_var(name("positive"), goal)
    terms = list(synthes_memory(ctx, 1, goal, lambda n: n.name not in ("wrap", "positive"), {}, conditionals=False))
    assert terms
    assert any(check_type(ctx, term, goal) for term in terms)


def test_contextual_argument_facts_prune_a_nontrivial_partial_application():
    from aeon.core.types import ExistentialType
    from aeon.typechecking.typeinfer import synth

    identity = parse_type("(x:Int) -> {v:Int | v == x}")
    ctx = built_std_context().with_var(name("f"), identity).with_var(name("g"), identity)
    argument = Application(Var(name("g")), Application(Var(name("f")), Literal(6, t_int)))
    assert isinstance(synth(ctx, argument)[1], ExistentialType)
    fn = parse_type("(x:Int) -> (y:{v:Int | v >= 0}) -> {v:Int | v == (x + y)}")
    goal = parse_type("{v:Int | v == 5}")
    app = ApplicationState.start(ConstraintState(ctx), fn, goal)
    assert app.check() == Status.VALID
    chosen = app.choose(argument)
    assert chosen.check() == Status.INVALID
    assert len(chosen.params) == 1
