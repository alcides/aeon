"""Example repairs must preserve verification and runtime fitness contracts."""

from pathlib import Path
import math

import pytest

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.multiplicity import MOmega
from aeon.core.terms import Abstraction, Literal, Rec
from aeon.core.types import AbstractionType, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.linearity import check_linearity
from aeon.utils.name import Name
from aeon.verification.horn import get_possible_args
from aeon.verification.smt import rename_constraint, smt_valid
from aeon.verification.vcs import Conjunction, Implication, LiquidConstraint, alpha_key

ROOT = Path(__file__).resolve().parents[1]


def driver(*, check=True):
    return AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 1, no_main=True, check_only=check))


@pytest.mark.parametrize(
    "body,expected",
    [
        ("?h", True),
        ("if b then ?h else x", True),
        ("if b then x else ?h", True),
        ("let y := x in ?h", True),
        ("let y := x + x in ?h", False),
        ("if b then x + x else ?h", False),
        ("0", False),
        ("x", True),
    ],
)
def test_linear_holes_defer_missing_uses_but_not_known_duplicates(body, expected):
    errors = list(driver().parse(aeon_code=f"def f (1 x:Int) (b:Bool) : Int := {body};"))
    assert (not errors) is expected


def test_hole_cannot_erase_a_known_runtime_use():
    assert list(driver().parse(aeon_code="def f (0 x:Int) : Int := let y := x + 1 in ?h;"))


def test_unrestricted_bindings_do_not_tally_their_entire_tail(monkeypatch):
    def forbidden(*args, **kwargs):
        pytest.fail("Unrestricted binders need traversal, not repeated usage tallies")

    monkeypatch.setattr("aeon.typechecking.linearity._Walker.tally", forbidden)
    x, f = Name("x", 1), Name("f", 2)
    core = Rec(
        f, AbstractionType(x, t_int, t_int), Abstraction(x, Literal(1, t_int)), Literal(0, t_int), multiplicity=MOmega
    )
    assert not check_linearity(core)


def test_constraint_renaming_preserves_shared_dag():
    old, new = Name("x", 1), Name("x", 2)
    node = LiquidConstraint(LiquidVar(old))
    for _ in range(25):
        node = Conjunction(node, node)
    result = rename_constraint(node, old, new)
    for _ in range(25):
        assert isinstance(result, Conjunction)
        assert result.c1 is result.c2
        result = result.c1
    assert result.expr == LiquidVar(new)


def test_streamed_alpha_key_preserves_scopes_and_numbering():
    x, y = Name("x", 10), Name("x", 99)
    eq = Name("==", 0)
    constraint = Conjunction(
        Implication(
            x, t_int, LiquidLiteralBool(True), LiquidConstraint(LiquidApp(eq, [LiquidVar(x), LiquidLiteralInt(1)]))
        ),
        Implication(
            y, t_int, LiquidLiteralBool(True), LiquidConstraint(LiquidApp(eq, [LiquidVar(y), LiquidLiteralInt(2)]))
        ),
    )
    assert alpha_key(constraint) == "(∀x#0:Int, (true) => (x#0 == 1)) ∧ (∀x#1:Int, (true) => (x#1 == 2))"


def test_shadowed_smt_binder_does_not_reuse_outer_value():
    x, eq = Name("x", 0), Name("==", 0)

    def equals(value):
        return LiquidApp(eq, [LiquidVar(x), LiquidLiteralInt(value)])

    bad = Implication(x, t_int, equals(1), Implication(x, t_int, equals(2), LiquidConstraint(equals(1))))
    assert not smt_valid(bad)


def test_horn_argument_generation_deduplicates_without_losing_atoms():
    variables = [(LiquidVar(Name(f"x{i}")), t_int) for i in range(20)]
    args = list(get_possible_args(variables, arity=2))
    assert len(args) == 24 * 24
    assert len({tuple(a) for a in args}) == len(args)
    assert [LiquidLiteralInt(0), LiquidLiteralInt(1)] in args


@pytest.mark.parametrize(
    "helper,values,expected",
    [
        ("objective_errors", "#[1, 2]", "[1.0, 2.0]"),
        ("objective_errors", "#[1.5, 2.25]", "[1.5, 2.25]"),
        ("objective_errors_int", "#[1, 2]", "[1, 2]"),
    ],
)
def test_psb2_objective_vector_has_real_runtime_shape(helper, values, expected):
    d = driver(check=False)
    src = f"""import PSB2;
def main (_:Int) : Bool :=
    let 1 xs := PSB2.{helper} {values} 2 in native "xs == {expected}";"""
    assert not d.parse(aeon_code=src)
    assert d.run() is True


def test_psb2_objective_vector_rejects_wrong_runtime_length():
    d = driver(check=False)
    src = """import PSB2; import Array;
def main (_:Int) : Int :=
    let 1 xs := PSB2.objective_errors #[1] 2 in Array.length xs;"""
    assert not d.parse(aeon_code=src)
    with pytest.raises(ValueError, match="unexpected PSB2 objective count"):
        d.run()


@pytest.mark.parametrize("task,length", [("coin_sum", 200), ("cut_vector", 200), ("leaders", 50)])
def test_psb2_goal_counts_training_cases_not_output_arity(task, length):
    d = driver()
    assert not d.parse(filename=str(ROOT / f"examples/PSB2/annotations/multi_objective/{task}.ae"))
    goals = [g for entry in d.metadata.values() for g in entry.get("goals", [])]
    assert len(goals) == 1 and goals[0].length == length


def test_refinement_constants_do_not_execute_unrelated_native_code():
    d = driver()
    source = 'def unrelated : Int := native "1 / 0"; def f (x:{v:Int | v > 1 + 2}) : Int := x;'
    assert not d.parse(aeon_code=source)


def test_constructor_type_arguments_follow_declaration_not_alphabetical_order():
    source = """inductive Duo z a
| mk (left:z) (right:a) : (Duo z a)
def pair (_:Unit) : (Duo Int Bool) := (Duo.mk{Int}{Bool}) 7 true;"""
    assert not driver().parse(aeon_code=source)


def test_elaboration_preserves_explicit_refinement_instead_of_inventing_a_horn_hole():
    from aeon.elaboration import elaborate_remove_unification
    from aeon.elaboration.context import ElaborationTypingContext
    from aeon.sugar.equality import type_equality
    from aeon.sugar.parser import parse_expression, parse_type

    ctx = ElaborationTypingContext().with_var(Name("identity"), parse_type("forall t:B, (x:t) -> t"))
    term = parse_expression("identity{{v:Int | v > 0}}")
    result = elaborate_remove_unification(ctx, term)
    assert type_equality(result.type, term.type)


@pytest.mark.parametrize("start,end,eccentricity", [(0.0, 90.0, 0.0), (270.0, 90.0, 0.5), (45.0, 315.0, 0.9)])
def test_guarded_planet_calculation_preserves_the_numerical_result(start, end, eccentricity):
    def mean(degrees):
        angle = math.radians(degrees)
        eccentric = (
            math.atan2(math.sqrt(1 - eccentricity**2) * math.sin(angle), eccentricity + math.cos(angle)) % math.tau
        )
        return eccentric - eccentricity * math.sin(eccentric)

    delta = abs(mean(end) - mean(start)) / math.tau
    expected = min(delta, 1 - delta)
    path = ROOT / "examples/bugs/planet_orbit.ae"
    source = path.read_text().split("def main", 1)[0]
    source += f"def main (_:Int) : Float := min_elapsed_period_fraction {start} {end} {eccentricity};"
    d = driver(check=False)
    assert not d.parse(aeon_code=source, filename=str(path))
    assert d.run() == pytest.approx(expected)
