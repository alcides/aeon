"""Tests for aeon.typechecking.liquid — liquid type inference and checking."""

from __future__ import annotations

import pytest

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidVar,
)
from aeon.core.types import (
    AbstractionType,
    LiquidHornApplication,
    RefinedType,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    t_bool,
    t_float,
    t_int,
    t_string,
    t_unit,
    BaseKind,
)
from aeon.typechecking.context import TypingContext
from aeon.typechecking.liquid import (
    LiquidTypeCheckException,
    LiquidTypeCheckingContext,
    check_liquid,
    lower_abstraction_type,
    lower_context,
    type_infer_liquid,
    typecheck_liquid,
)
from aeon.utils.name import Name


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

x = Name("x")
y = Name("y")
z = Name("z")
f = Name("f")


def _lctx(
    variables: dict[Name, TypeConstructor | TypeVar] | None = None,
    functions: dict[Name, list[TypeConstructor | TypeVar]] | None = None,
) -> LiquidTypeCheckingContext:
    return LiquidTypeCheckingContext(
        known_types=[t_int, t_bool, t_float, t_string, t_unit],
        variables=variables or {},
        functions=functions
        or {
            Name("+"): [t_int, t_int, t_int],
            Name("-"): [t_int, t_int, t_int],
            Name("*"): [t_int, t_int, t_int],
            Name("/"): [t_int, t_int, t_int],
            Name("=="): [t_int, t_int, t_bool],
            Name("!="): [t_int, t_int, t_bool],
            Name("<"): [t_int, t_int, t_bool],
            Name("<="): [t_int, t_int, t_bool],
            Name(">"): [t_int, t_int, t_bool],
            Name(">="): [t_int, t_int, t_bool],
            Name("&&"): [t_bool, t_bool, t_bool],
            Name("||"): [t_bool, t_bool, t_bool],
            Name("!"): [t_bool, t_bool],
        },
    )


# ---------------------------------------------------------------------------
# type_infer_liquid: literals
# ---------------------------------------------------------------------------


def test_infer_literal_int():
    assert type_infer_liquid(_lctx(), LiquidLiteralInt(42)) == t_int


def test_infer_literal_bool():
    assert type_infer_liquid(_lctx(), LiquidLiteralBool(True)) == t_bool


def test_infer_literal_float():
    assert type_infer_liquid(_lctx(), LiquidLiteralFloat(3.14)) == t_float


def test_infer_literal_string():
    assert type_infer_liquid(_lctx(), LiquidLiteralString("hi")) == t_string


# ---------------------------------------------------------------------------
# type_infer_liquid: variables
# ---------------------------------------------------------------------------


def test_infer_var_found():
    ctx = _lctx(variables={x: t_int})
    assert type_infer_liquid(ctx, LiquidVar(x)) == t_int


def test_infer_var_not_found():
    ctx = _lctx()
    with pytest.raises(LiquidTypeCheckException, match="not in context"):
        type_infer_liquid(ctx, LiquidVar(x))


# ---------------------------------------------------------------------------
# type_infer_liquid: function application
# ---------------------------------------------------------------------------


def test_infer_app_plus():
    ctx = _lctx(variables={x: t_int, y: t_int})
    term = LiquidApp(Name("+"), [LiquidVar(x), LiquidVar(y)])
    assert type_infer_liquid(ctx, term) == t_int


def test_infer_app_comparison():
    ctx = _lctx(variables={x: t_int, y: t_int})
    term = LiquidApp(Name("<"), [LiquidVar(x), LiquidVar(y)])
    assert type_infer_liquid(ctx, term) == t_bool


def test_infer_app_unknown_function():
    ctx = _lctx(variables={x: t_int})
    term = LiquidApp(Name("unknown_fn"), [LiquidVar(x)])
    with pytest.raises(LiquidTypeCheckException, match="not in context"):
        type_infer_liquid(ctx, term)


def test_infer_app_wrong_arity():
    ctx = _lctx(variables={x: t_int})
    term = LiquidApp(Name("+"), [LiquidVar(x)])  # needs 2 args
    with pytest.raises(LiquidTypeCheckException, match="arguments"):
        type_infer_liquid(ctx, term)


def test_infer_app_type_mismatch():
    ctx = _lctx(variables={x: t_bool})
    term = LiquidApp(Name("+"), [LiquidVar(x), LiquidLiteralInt(1)])
    with pytest.raises(LiquidTypeCheckException):
        type_infer_liquid(ctx, term)


def test_infer_nested_app():
    ctx = _lctx(variables={x: t_int, y: t_int})
    # (x + y) > 0
    inner = LiquidApp(Name("+"), [LiquidVar(x), LiquidVar(y)])
    outer = LiquidApp(Name(">"), [inner, LiquidLiteralInt(0)])
    assert type_infer_liquid(ctx, outer) == t_bool


# ---------------------------------------------------------------------------
# type_infer_liquid: polymorphic functions
# ---------------------------------------------------------------------------


def test_infer_polymorphic_eq():
    a = Name("a")
    ctx = _lctx(
        variables={x: t_int, y: t_int},
        functions={Name("=="): [TypeVar(a), TypeVar(a), t_bool]},
    )
    term = LiquidApp(Name("=="), [LiquidVar(x), LiquidVar(y)])
    assert type_infer_liquid(ctx, term) == t_bool


def test_infer_polymorphic_eq_mismatch():
    a = Name("a")
    ctx = _lctx(
        variables={x: t_int, y: t_bool},
        functions={Name("=="): [TypeVar(a), TypeVar(a), t_bool]},
    )
    term = LiquidApp(Name("=="), [LiquidVar(x), LiquidVar(y)])
    with pytest.raises(LiquidTypeCheckException):
        type_infer_liquid(ctx, term)


# ---------------------------------------------------------------------------
# type_infer_liquid: horn application
# ---------------------------------------------------------------------------


def test_infer_horn_application():
    ctx = _lctx()
    horn = LiquidHornApplication(Name("k"), [(LiquidVar(x), t_int)])
    assert type_infer_liquid(ctx, horn) == t_bool


# ---------------------------------------------------------------------------
# check_liquid
# ---------------------------------------------------------------------------


def test_check_liquid_success():
    ctx = _lctx(variables={x: t_int})
    term = LiquidApp(Name(">"), [LiquidVar(x), LiquidLiteralInt(0)])
    assert check_liquid(ctx, term, t_bool) is True


def test_check_liquid_wrong_type():
    ctx = _lctx(variables={x: t_int})
    term = LiquidApp(Name("+"), [LiquidVar(x), LiquidLiteralInt(1)])
    assert check_liquid(ctx, term, t_bool) is False  # result is Int, not Bool


def test_check_liquid_returns_false_on_error():
    ctx = _lctx()
    term = LiquidVar(Name("nonexistent"))
    assert check_liquid(ctx, term, t_bool) is False


# ---------------------------------------------------------------------------
# lower_abstraction_type
# ---------------------------------------------------------------------------


def test_lower_simple_arrow():
    # (x:Int) -> Bool
    ty = AbstractionType(x, t_int, t_bool)
    result = lower_abstraction_type(ty)
    assert result == [t_int, t_bool]


def test_lower_multi_arrow():
    # (x:Int) -> (y:Int) -> Bool
    ty = AbstractionType(x, t_int, AbstractionType(y, t_int, t_bool))
    result = lower_abstraction_type(ty)
    assert result == [t_int, t_int, t_bool]


def test_lower_refined_arrow():
    # (x:{v:Int | v > 0}) -> Int
    refined = RefinedType(Name("v"), t_int, LiquidApp(Name(">"), [LiquidVar(Name("v")), LiquidLiteralInt(0)]))
    ty = AbstractionType(x, refined, t_int)
    result = lower_abstraction_type(ty)
    assert result == [t_int, t_int]


def test_lower_polymorphic_type():
    a = Name("a")
    # forall a. (x:a) -> a
    ty = TypePolymorphism(a, BaseKind(), AbstractionType(x, TypeVar(a), TypeVar(a)))
    result = lower_abstraction_type(ty)
    assert len(result) >= 2


# ---------------------------------------------------------------------------
# lower_context
# ---------------------------------------------------------------------------


def test_lower_context_basic():
    ctx = TypingContext()
    ctx = ctx.with_var(x, t_int)
    ctx = ctx.with_var(y, t_bool)
    lctx = lower_context(ctx)
    assert x in lctx.variables
    assert y in lctx.variables
    assert lctx.variables[x] == t_int
    assert lctx.variables[y] == t_bool


def test_lower_context_with_function():
    ctx = TypingContext()
    fn_ty = AbstractionType(x, t_int, t_int)
    ctx = ctx.with_var(f, fn_ty)
    lctx = lower_context(ctx)
    assert f in lctx.functions
    assert lctx.functions[f] == [t_int, t_int]


def test_lower_context_refined_var():
    ctx = TypingContext()
    refined = RefinedType(Name("v"), t_int, LiquidLiteralBool(True))
    ctx = ctx.with_var(x, refined)
    lctx = lower_context(ctx)
    assert x in lctx.variables
    assert lctx.variables[x] == t_int


# ---------------------------------------------------------------------------
# typecheck_liquid (integration with TypingContext)
# ---------------------------------------------------------------------------


def test_typecheck_liquid_with_typing_context():
    ctx = TypingContext()
    ctx = ctx.with_var(x, t_int)
    result = typecheck_liquid(ctx, LiquidVar(x))
    assert result == t_int


def test_typecheck_liquid_literal():
    ctx = TypingContext()
    result = typecheck_liquid(ctx, LiquidLiteralInt(5))
    assert result == t_int


# ---------------------------------------------------------------------------
# Operator restriction checks
# ---------------------------------------------------------------------------


def test_comparison_rejects_non_numeric():
    """< with polymorphic signature rejects String args via the operator restriction."""
    a = Name("a")
    ctx = _lctx(
        variables={x: t_string, y: t_string},
        functions={Name("<"): [TypeVar(a), TypeVar(a), t_bool]},
    )
    term = LiquidApp(Name("<"), [LiquidVar(x), LiquidVar(y)])
    with pytest.raises(LiquidTypeCheckException, match="Floats or Ints"):
        type_infer_liquid(ctx, term)


def test_arithmetic_rejects_bool():
    """+ with polymorphic signature rejects Bool args via the operator restriction."""
    a = Name("a")
    ctx = _lctx(
        variables={x: t_bool},
        functions={Name("+"): [TypeVar(a), TypeVar(a), TypeVar(a)]},
    )
    term = LiquidApp(Name("+"), [LiquidVar(x), LiquidVar(x)])
    with pytest.raises(LiquidTypeCheckException, match="Floats or Ints"):
        type_infer_liquid(ctx, term)


def test_eq_accepts_string():
    ctx = _lctx(
        variables={x: t_string, y: t_string},
        functions={Name("=="): [t_string, t_string, t_bool]},
    )
    term = LiquidApp(Name("=="), [LiquidVar(x), LiquidVar(y)])
    assert type_infer_liquid(ctx, term) == t_bool
