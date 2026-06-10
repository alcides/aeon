from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralUnit
from aeon.core.liquid import LiquidVar
from aeon.core.types import TypeConstructor
from aeon.core.types import AbstractionType
from aeon.core.types import Kind
from aeon.core.types import RefinementPolymorphism
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.core.types import t_int
from aeon.core.types import t_bool
from aeon.core.types import t_unit
from aeon.core.terms import Abstraction, Application, RefinementAbstraction, Var
from aeon.sugar.stypes import SRefinedType
from aeon.verification.smt import smt_valid
from aeon.verification.smt import flatten
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from aeon.verification.vcs import ReflectedFunctionDeclaration
from aeon.verification.sub import implication_constraint
from aeon.typechecking.typeinfer import _reflected_impl_for
from tests.driver import check_compile, check_compile_expr
from aeon.sugar.parser import parse_expression
from aeon.sugar.ast_helpers import st_int, st_top, st_bool
from aeon.utils.name import Name

name_a = Name("a", 102)
name_x = Name("x", 103)
name_y = Name("y", 104)
example = Implication(
    name_x,
    t_int,
    LiquidApp(Name("==", 0), [LiquidVar(name_x), LiquidLiteralInt(3)]),
    LiquidConstraint(
        LiquidApp(
            Name("==", 0),
            [LiquidVar(name_x), LiquidLiteralInt(3)],
        ),
    ),
)


def test_smt_example3():
    assert smt_valid(example)


example2 = Implication(
    name_x,
    TypeConstructor(name_a),
    LiquidLiteralBool(True),
    Implication(
        name_y,
        TypeConstructor(name_a),
        LiquidApp(Name("==", 0), [LiquidVar(name_x), LiquidVar(name_y)]),
        LiquidConstraint(
            LiquidApp(
                Name("==", 0),
                [LiquidVar(name_x), LiquidVar(name_y)],
            ),
        ),
    ),
)


def test_other_sorts():
    assert smt_valid(example2)


# Regression for issue #296: Unit must have its own SMT sort, distinct
# from Bool. Previously ``Literal((), Unit)`` was lowered to the boolean
# literal True, so ``unit == True`` came out satisfiable.
unit_eq_unit = LiquidConstraint(
    LiquidApp(Name("==", 0), [LiquidLiteralUnit(), LiquidLiteralUnit()]),
)


def test_unit_literal_equals_itself():
    assert smt_valid(unit_eq_unit)


name_u = Name("u", 200)
unit_var_eq_unit = Implication(
    name_u,
    t_unit,
    LiquidLiteralBool(True),
    LiquidConstraint(
        LiquidApp(Name("==", 0), [LiquidVar(name_u), LiquidLiteralUnit()]),
    ),
)


def test_unit_variable_equals_unit_literal():
    # Unit has a single inhabitant, so any value of sort Unit equals ().
    assert smt_valid(unit_var_eq_unit)


def test_unit_sort_is_not_bool():
    # Distinct z3 sorts: comparing the Unit constant against a Bool would
    # be a sort mismatch, but more importantly the previous encoding made
    # ``Unit`` and ``Bool``-true the same z3 term, which this prevents.
    from aeon.verification.smt import _unit_sort_ref
    from z3 import BoolSort

    assert _unit_sort_ref != BoolSort()


def test_uninterpreted() -> None:
    aeon_code = """
type List;
def List_size: (l:List) -> Int := uninterpreted;

def List_new : {x:List | List_size x = 0} := native "[]" ;

def List_append (l:List) (i: Int) : {l2:List | List_size l2 = (List_size l) + 1} := native "l + [i]"

def main (x:Int) : Unit :=
    empty := List_new;
    one := List_append empty 3;
    print(one)
"""
    check_compile(aeon_code, st_top)


def test_uninterpreted2() -> None:
    aeon_code = """
type List;
def List_size: (l:List) -> Int := uninterpreted;
def List_new : {u:List | List_size u = 0} := native "[]" ;
def List_append (l:List) (i: Int) : {l2:List | List_size l2 = List_size l + 1} := native "l + [i]"

def main (x:Int) : Unit :=
    empty := List_new;
    one := List_append empty 3;
    print(one)
"""
    check_compile(aeon_code, st_top)


def test_poly_to_smt():
    expected_stype = SRefinedType(Name("y"), st_bool, parse_expression("y = (x > (9 - z))"))

    assert check_compile_expr(
        "(x + z) > 9",
        expected_stype,
        extra_vars={
            Name("x"): st_int,
            Name("z"): st_int,
        },
    )


def test_reflected_function_unfolding() -> None:
    inc_name = Name("inc")
    x_name = Name("x")
    reflected_inc = ReflectedFunctionDeclaration(
        inc_name,
        AbstractionType(x_name, t_int, t_int),
        (x_name,),
        LiquidApp(Name("+", 0), [LiquidVar(x_name), LiquidLiteralInt(1)]),
        Implication(
            x_name,
            t_int,
            LiquidLiteralBool(True),
            LiquidConstraint(LiquidApp(Name(">", 0), [LiquidApp(inc_name, [LiquidVar(x_name)]), LiquidVar(x_name)])),
        ),
    )
    assert smt_valid(reflected_inc)


def test_native_function_is_not_reflected() -> None:
    aeon_code = """
def native_inc (x:Int) : Int := native "x + 1";

def witness (x:Int) : {v:Int | v > x} := native_inc x;

def main (x:Int) : Unit := print(witness x)
"""
    assert not check_compile(aeon_code, st_top)


def test_rank2_reflected_unfolding() -> None:
    a = Name("a")
    x = Name("x")
    poly_id = TypePolymorphism(a, Kind.BASE, AbstractionType(x, TypeVar(a), TypeVar(a)))
    reflected = implication_constraint(
        Name("id"),
        poly_id,
        LiquidConstraint(LiquidLiteralBool(True)),
        reflected_impl=((x,), LiquidVar(x)),
    )
    assert isinstance(reflected, ReflectedFunctionDeclaration)
    vc = implication_constraint(
        x,
        t_int,
        LiquidConstraint(LiquidApp(Name("==", 0), [LiquidApp(Name("id"), [LiquidVar(x)]), LiquidVar(x)])),
    )
    assert smt_valid(ReflectedFunctionDeclaration(Name("id"), reflected.type, (x,), LiquidVar(x), vc))


def test_rank3_reflected_unfolding() -> None:
    t = Name("t")
    f = Name("f")
    g = Name("g")
    n = Name("n")
    rank3_ty = TypePolymorphism(
        f,
        Kind.BASE,
        AbstractionType(
            g,
            TypePolymorphism(t, Kind.BASE, AbstractionType(Name("x"), TypeVar(t), TypeVar(t))),
            AbstractionType(n, TypeVar(f), TypeVar(f)),
        ),
    )
    reflected = implication_constraint(
        Name("passPoly"),
        rank3_ty,
        LiquidConstraint(LiquidLiteralBool(True)),
        reflected_impl=((g, n), LiquidVar(n)),
    )
    assert isinstance(reflected, ReflectedFunctionDeclaration)


def test_polymorphic_reflection_specializes_multiple_instances() -> None:
    a = Name("a")
    x = Name("x")
    id_name = Name("id")
    poly_id = TypePolymorphism(a, Kind.BASE, AbstractionType(x, TypeVar(a), TypeVar(a)))
    base = implication_constraint(
        id_name,
        poly_id,
        Conjunction(
            LiquidConstraint(
                LiquidApp(Name("==", 0), [LiquidApp(id_name, [LiquidLiteralInt(1)]), LiquidLiteralInt(1)])
            ),
            LiquidConstraint(
                LiquidApp(Name("==", 0), [LiquidApp(id_name, [LiquidLiteralFloat(1.0)]), LiquidLiteralFloat(1.0)])
            ),
        ),
        reflected_impl=((x,), LiquidVar(x)),
    )
    assert smt_valid(base)
    cans = list(flatten(base))
    assert any("__spec__Int" in name or "__spec__Float" in name for c in cans for name in c.functions.keys())


def test_refinement_polymorphic_reflection_supported() -> None:
    p = Name("p")
    x = Name("x")
    ty = RefinementPolymorphism(p, t_int, AbstractionType(x, t_int, t_int))
    reflected = implication_constraint(
        Name("rid"),
        ty,
        LiquidConstraint(LiquidLiteralBool(True)),
        reflected_impl=((x,), LiquidVar(x)),
    )
    assert isinstance(reflected, ReflectedFunctionDeclaration)


def test_refinement_polymorphic_reflection_rejects_predicate_dependent_body() -> None:
    p = Name("p")
    x = Name("x")
    impl = RefinementAbstraction(
        p,
        t_int,
        Abstraction(
            x,
            Application(Var(p), Var(x)),
        ),
    )
    ty = RefinementPolymorphism(p, t_int, AbstractionType(x, t_int, t_bool))
    assert _reflected_impl_for(Name("rid"), ty, impl) is None


def test_recursive_reflection_requires_termination_metric() -> None:
    f = Name("f")
    x = Name("x")
    ty = AbstractionType(x, t_int, t_int)
    impl = Abstraction(x, Application(Var(f), Var(x)))
    assert _reflected_impl_for(f, ty, impl, has_termination_metric=False) is None
    assert _reflected_impl_for(f, ty, impl, has_termination_metric=True) is not None


def test_division_by_zero_is_not_vacuously_valid() -> None:
    # `-2 / 0` is undefined: it crashes at runtime and Z3 leaves it
    # unconstrained. A proof obligation that depends on it must NOT be reported
    # valid by silently skipping it. Regression: absurd refinements slipped
    # through (e.g. a literal `/ 0` "satisfying" any spec).
    div0 = LiquidApp(Name("/", 0), [LiquidLiteralInt(-2), LiquidLiteralInt(0)])
    claim = LiquidConstraint(LiquidApp(Name(">=", 0), [div0, LiquidLiteralInt(0)]))
    assert smt_valid(claim) is False


def test_modulo_by_zero_is_not_vacuously_valid() -> None:
    mod0 = LiquidApp(Name("%", 0), [LiquidLiteralInt(5), LiquidLiteralInt(0)])
    claim = LiquidConstraint(LiquidApp(Name("==", 0), [mod0, LiquidLiteralInt(0)]))
    assert smt_valid(claim) is False


def test_division_by_nonzero_still_valid() -> None:
    # The fix must not over-reject: a well-defined division obligation that is
    # genuinely true stays valid.
    div = LiquidApp(Name("/", 0), [LiquidLiteralInt(6), LiquidLiteralInt(2)])
    claim = LiquidConstraint(LiquidApp(Name("==", 0), [div, LiquidLiteralInt(3)]))
    assert smt_valid(claim) is True
