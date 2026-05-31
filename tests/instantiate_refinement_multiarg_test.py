"""Tests for multi-argument predicate inlining in `instantiate_refinement_in_liquid`.

See issue #297: `κ(x1, ..., xn)[ρ := φ]` should inline a curried refinement
`φ = λy1...yn. p` to `p[y1 := x1, ..., yn := xn]`, not just the single-arg case.
"""

from aeon.core.liquid import LiquidApp, LiquidVar
from aeon.core.substitutions import instantiate_refinement_in_liquid
from aeon.core.terms import Abstraction, Application, Var
from aeon.utils.name import Name


def _lt(a: Name, b: Name) -> Application:
    """The core term `a < b`, curried: ((< a) b)."""
    return Application(Application(Var(Name("<", 0)), Var(a)), Var(b))


def test_single_arg_predicate_still_inlines():
    """Regression: the original single-argument path keeps working."""
    pred = Name("k", 1)
    y = Name("y", 2)
    x = Name("x", 3)
    # φ = λy. (y < y)  ; instantiate k(x)
    refinement = Abstraction(y, _lt(y, y))
    term = LiquidApp(pred, [LiquidVar(x)])

    result = instantiate_refinement_in_liquid(term, pred, refinement)

    assert result == LiquidApp(Name("<", 0), [LiquidVar(x), LiquidVar(x)])


def test_two_arg_predicate_inlines():
    """φ = λa. λb. (a < b) ; k(x, z) should become (x < z)."""
    pred = Name("k", 1)
    a = Name("a", 2)
    b = Name("b", 3)
    x = Name("x", 4)
    z = Name("z", 5)
    refinement = Abstraction(a, Abstraction(b, _lt(a, b)))
    term = LiquidApp(pred, [LiquidVar(x), LiquidVar(z)])

    result = instantiate_refinement_in_liquid(term, pred, refinement)

    assert result == LiquidApp(Name("<", 0), [LiquidVar(x), LiquidVar(z)])


def test_arity_mismatch_falls_through():
    """If the curried refinement has fewer binders than the application has
    arguments, the predicate is left untouched (recursing into its args)."""
    pred = Name("k", 1)
    a = Name("a", 2)
    x = Name("x", 4)
    z = Name("z", 5)
    # Only one binder, but two arguments supplied.
    refinement = Abstraction(a, _lt(a, a))
    term = LiquidApp(pred, [LiquidVar(x), LiquidVar(z)])

    result = instantiate_refinement_in_liquid(term, pred, refinement)

    assert result == LiquidApp(pred, [LiquidVar(x), LiquidVar(z)])


def test_nested_predicate_application_is_inlined():
    """A multi-arg predicate nested as an argument of another app is inlined."""
    pred = Name("k", 1)
    a = Name("a", 2)
    b = Name("b", 3)
    x = Name("x", 4)
    z = Name("z", 5)
    refinement = Abstraction(a, Abstraction(b, _lt(a, b)))
    inner = LiquidApp(pred, [LiquidVar(x), LiquidVar(z)])
    term = LiquidApp(Name("&&", 0), [inner])

    result = instantiate_refinement_in_liquid(term, pred, refinement)

    assert result == LiquidApp(Name("&&", 0), [LiquidApp(Name("<", 0), [LiquidVar(x), LiquidVar(z)])])
