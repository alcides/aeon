"""Keep nested inference and generated vector spines within CI bounds."""

import re

import pytest
from hypothesis import given, settings, strategies as st

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Application
from aeon.core.types import AbstractionType, ExistentialType, Kind, TypePolymorphism, TypeVar, t_bool, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.liquid import lower_context, typecheck_liquid
from aeon.utils.name import Name
from scripts.compact_hakank_sequences import compact
from scripts.generate_hakank_examples import Model, share_decision_accesses


def test_nested_application_infers_each_argument_once(monkeypatch):
    import aeon.typechecking.typeinfer as inference

    original = inference._synth
    visits = 0

    def counted(ctx, term):
        nonlocal visits
        if isinstance(term, Application):
            visits += 1
        return original(ctx, term)

    monkeypatch.setattr(inference, "_synth", counted)
    expression = "1"
    depth = 6
    for _ in range(depth):
        expression = f"combine ({expression}) ({expression})"
    source = f"def combine (x:Int) (y:Int) : Int := x + y; def answer : Int := {expression};"
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 1, check_only=True, no_main=True))
    assert not driver.parse(aeon_code=source)
    assert visits < 8 * 2**depth


def test_targeted_liquid_context_keeps_existential_binders():
    x, wrapper = Name("x", 1), Name("wrapper", 2)
    ctx = TypingContext().with_var(wrapper, ExistentialType(((x, t_int),), t_int))
    assert typecheck_liquid(ctx, LiquidVar(x)) == t_int


def test_targeted_liquid_context_preserves_polymorphic_function_lookup():
    x, f, a = Name("x", 1), Name("f", 2), Name("a", 3)
    ty = TypePolymorphism(a, Kind.BASE, AbstractionType(x, TypeVar(a), t_bool))
    ctx = TypingContext().with_var(f, ty).with_var(x, t_int)
    term = LiquidApp(f, [LiquidLiteralInt(1)])
    assert typecheck_liquid(ctx, term) == t_bool
    assert lower_context(ctx, {f}).functions == {f: [TypeVar(a), t_bool]}


def test_argument_capture_is_reset_after_type_error():
    import aeon.typechecking.typeinfer as inference

    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 1, check_only=True, no_main=True))
    assert driver.parse(aeon_code='def f (x:Int) : Int := x; def bad : Int := f ("wrong");')
    assert inference._argument_inference.get() is None


@pytest.mark.parametrize("length", [33, 64, 65, 100, 1000])
def test_vector_compaction_preserves_order_and_matches_generator(length):
    source = ""
    tail = "Vec.nil"
    for index in reversed(range(length)):
        name = f"sequence0_tail{index}"
        source += f"def {name} : (Vec Int) := Vec.cons ({index}) ({tail});\n"
        tail = name
    source += "def valid : Bool := Vec.sum sequence0_tail0 = 0;\n"
    result = compact(source)
    assert compact(result) == result
    assert [int(n) for n in re.findall(r"Vec.cons \((\d+)\)", result)] == [
        n for start in reversed(range(0, length, 32)) for n in range(start, min(start + 32, length))
    ]
    model = Model("fixture", "sequence migration")
    model.sequence([str(i) for i in range(length)])
    generated = model.render({"source_url": "https://example.org/fixture"})
    assert [line for line in result.splitlines() if line.startswith("def sequence")] == [
        line for line in generated.splitlines() if line.startswith("def sequence")
    ]


def test_compaction_keeps_shared_or_publicly_referenced_tails():
    source = """def sequence0_tail2 : (Vec Int) := Vec.cons (2) (Vec.nil);
def sequence0_tail1 : (Vec Int) := Vec.cons (1) (sequence0_tail2);
def sequence0_tail0 : (Vec Int) := Vec.cons (0) (sequence0_tail1);
def suffix : (Vec Int) := sequence0_tail1;
"""
    result = compact(source)
    assert "def sequence0_tail1" in result
    assert "def suffix : (Vec Int) := sequence0_tail1;" in result


@pytest.mark.parametrize("result,accepted", [("v >= 0", True), ("v < 0", False)])
def test_conditional_numeric_witnesses_keep_branch_guards(result, accepted):
    source = f"""def identity (x:Int) : Int := x;
def magnitude (x:Int) : {{v:Int | {result}}} :=
    let r := if x < 0 then 0 - (identity x) else identity x in r;"""
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 1, check_only=True, no_main=True))
    assert (not driver.parse(aeon_code=source)) is accepted


def test_deep_constraint_walkers_are_not_python_stack_bounded():
    from aeon.core.liquid import LiquidLiteralBool
    from aeon.verification.horn import contains_horn_constraint
    from aeon.verification.vcs import Implication, LiquidConstraint, alpha_key

    constraint = LiquidConstraint(LiquidLiteralBool(False))
    for index in range(12000):
        constraint = Implication(Name("deep", index), t_int, LiquidLiteralBool(True), constraint)
    assert not contains_horn_constraint(constraint)
    key = alpha_key(constraint)
    assert key.startswith("∀deep#0:Int, (true) => ")
    assert key.endswith("∀deep#11999:Int, (true) => false")


def test_unification_bound_graph_is_visited_once_per_query():
    from aeon.elaboration import UnificationVar, extract_direction
    from aeon.sugar.ast_helpers import st_int

    visits = 0

    class Bounds(list):
        def __add__(self, other):
            nonlocal visits
            visits += 1
            return super().__add__(other)

    graph = UnificationVar(Name("bound", 0), Bounds([st_int]), [])
    for index in range(1, 25):
        graph = UnificationVar(Name("bound", index), Bounds([graph, graph]), [])
    assert extract_direction(graph) == [st_int]
    assert visits == 25


def test_unification_bound_cycles_keep_ordered_reachable_types():
    from aeon.elaboration import UnificationVar, extract_direction
    from aeon.sugar.ast_helpers import st_bool, st_int

    a, b = UnificationVar(Name("a")), UnificationVar(Name("b"))
    a.lower = [b, st_bool]
    b.upper = [a, st_int]
    assert extract_direction(a) == [st_int, st_bool]


def test_unification_direction_memo_invalidates_transitive_bound_updates():
    from aeon.elaboration import UnificationVar, _direction_dependencies, _direction_memo, extract_direction
    from aeon.sugar.ast_helpers import st_bool, st_int

    child = UnificationVar(Name("child"), [st_int], [])
    root = UnificationVar(Name("root"), [child], [])
    token = _direction_memo.set({})
    dependency_token = _direction_dependencies.set(set())
    try:
        assert extract_direction(root) == [st_int]
        cached = _direction_memo.get()[id(root)]
        unrelated = UnificationVar(Name("unrelated"))
        unrelated.constrain_upper(st_bool)
        assert _direction_memo.get()[id(root)] is cached
        child.constrain_upper(st_bool)
        assert extract_direction(root) == [st_int, st_bool]
    finally:
        _direction_dependencies.reset(dependency_token)
        _direction_memo.reset(token)
    assert _direction_memo.get() is None


def test_constructor_view_tracks_entry_and_declaration_mutations():
    from aeon.typechecking.context import TypeConstructorBinder

    foo, bar, parameter = Name("Foo"), Name("Bar"), Name("a")
    original = TypeConstructorBinder(foo, [])
    parent = TypingContext([original])
    ctx = parent.with_var(Name("x"), t_int)
    assert ctx.get_type_constructor(foo) == []
    replacement = TypeConstructorBinder(foo, [parameter])
    ctx.entries.append(replacement)
    assert ctx.get_type_constructor(foo) == [parameter]
    ctx.entries.pop()
    assert ctx.get_type_constructor(foo) == []
    ctx.entries[ctx.entries.index(original)] = replacement
    assert ctx.get_type_constructor(foo) == [parameter]
    replacement.name = bar
    assert ctx.get_type_constructor(foo) is None
    assert ctx.get_type_constructor(bar) == [parameter]
    replacement.args.append(Name("b"))
    assert len(ctx.get_type_constructor(bar)) == 2
    # Entry lists remain independent, as before; declaration objects stay live.
    assert parent.get_type_constructor(foo) == []


def test_constructor_view_preserves_shadowing_after_list_reorder():
    from aeon.typechecking.context import TypeConstructorBinder

    foo, parameter = Name("Foo"), Name("a")
    ctx = TypingContext().with_var(Name("x"), t_int)
    ctx.entries.extend([TypeConstructorBinder(foo, []), TypeConstructorBinder(foo, [parameter])])
    assert ctx.get_type_constructor(foo) == [parameter]
    ctx.entries.reverse()
    assert ctx.get_type_constructor(foo) == []


@settings(max_examples=25)
@given(st.lists(st.integers(min_value=0, max_value=9), max_size=30))
def test_constructor_view_matches_list_semantics_after_mutations(operations):
    from aeon.typechecking.context import TypeConstructorBinder

    foo = Name("Foo")
    ctx = TypingContext().with_var(Name("x"), t_int)
    for index, operation in enumerate(operations):
        entry = TypeConstructorBinder(foo, [Name(f"p{index}")])
        ctx.get_type_constructor(foo)  # Populate the derived view before changing it.
        if operation == 0:
            ctx.entries.append(entry)
        elif operation == 1:
            ctx.entries.extend([entry])
        elif operation == 2:
            ctx.entries.insert(0, entry)
        elif operation == 3:
            ctx.entries[:] = [entry]
        elif operation == 4 and ctx.entries:
            del ctx.entries[0]
        elif operation == 5 and ctx.entries:
            ctx.entries.pop()
        elif operation == 6:
            ctx.entries.reverse()
        elif operation == 7:
            ctx.entries += [entry]
        elif operation == 8:
            ctx.entries *= 0
        elif operation == 9:
            ctx.entries.sort(key=repr)
        expected = next(
            (e.args for e in reversed(ctx.entries) if isinstance(e, TypeConstructorBinder) and e.name == foo), None
        )
        assert ctx.get_type_constructor(foo) == expected


def test_refinement_binder_sort_is_local_to_the_predicate():
    from aeon.core.liquid import LiquidLiteralBool

    x = Name("x", 1)
    numeric = LiquidApp(Name("<", 0), [LiquidVar(x), LiquidLiteralInt(2)])
    # The refinement's locally bound x:Int is not the outer x:Bool.
    comparator = AbstractionType(Name("left"), t_int, AbstractionType(Name("right"), t_int, t_bool))
    ctx = TypingContext().with_var(Name("<", 0), comparator).with_var(x, t_bool)
    assert typecheck_liquid(ctx, numeric, (x, t_int)) == t_bool
    assert typecheck_liquid(ctx, LiquidLiteralBool(True), (x, t_int)) == t_bool


def test_shared_projections_preserve_runtime_value_and_are_idempotent():
    source = (
        """import DecisionTree;
def decisionsInt : (DecisionTree Int) := DecisionTree.leaf 7;
def main (_:Int) : Int := """
        + " + ".join(["(DecisionTree.intAt 0 decisionsInt)"] * 12)
        + ";\n"
    )
    compacted = share_decision_accesses(source)
    assert "def _shared_decision_intAt_0 : Int" in compacted
    assert share_decision_accesses(compacted) == compacted
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 1, no_main=True))
    assert not driver.parse(aeon_code=compacted)
    assert driver.run() == 84


def test_sharing_keeps_all_holes_and_caps_alias_spine():
    model = Model("fixture", "shared projections")
    model.compact = True
    names = model.vector("decision", 20, 0, 9)
    model.constraints = [f"{name} >= 0" for name in names for _ in range(10)]
    source = model.render({"source_url": "https://example.org/fixture"})
    assert re.findall(r"\?h_\w+", source) == [f"?h_{name}" for name in names]
    assert len(re.findall(r"^def _shared_decision_", source, re.M)) == 20
