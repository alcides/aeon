"""Tests for aeon.typechecking.termination — termination metric constraints."""

from __future__ import annotations

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralInt,
    LiquidVar,
)
from aeon.core.terms import (
    Abstraction,
    Application,
    If,
    Literal,
    Rec,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    t_int,
)
from aeon.typechecking.termination import (
    _lexicographic_less,
    _liquefy_metric_at,
    collect_recursive_calls_with_paths,
    entry_refinement_liquids,
    peel_abstractions,
    peel_application_chain,
    peel_type_formal_names,
    substitute_formals,
    termination_metric_constraints,
)
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Conjunction, Implication, LiquidConstraint
from aeon.utils.name import Name


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

n = Name("n")
m = Name("m")
x = Name("x")
v = Name("v")
f = Name("f")

int_arrow_int = AbstractionType(n, t_int, t_int)
two_int_arrow_int = AbstractionType(m, t_int, AbstractionType(n, t_int, t_int))


def _var(name: Name) -> Var:
    return Var(name)


def _app(fun, arg) -> Application:
    return Application(fun, arg)


def _abs(name: Name, body) -> Abstraction:
    return Abstraction(name, body)


def _lit(val: int) -> Literal:
    return Literal(val, type=t_int)


def _if(cond, then, otherwise) -> If:
    return If(cond, then, otherwise)


# ---------------------------------------------------------------------------
# peel_abstractions
# ---------------------------------------------------------------------------


def test_peel_abstractions_simple():
    body = _lit(1)
    term = _abs(x, body)
    names, inner = peel_abstractions(term)
    assert names == [x]
    assert inner == body


def test_peel_abstractions_nested():
    body = _lit(1)
    term = _abs(x, _abs(n, body))
    names, inner = peel_abstractions(term)
    assert names == [x, n]
    assert inner == body


def test_peel_abstractions_no_abs():
    body = _lit(1)
    names, inner = peel_abstractions(body)
    assert names == []
    assert inner == body


# ---------------------------------------------------------------------------
# peel_type_formal_names
# ---------------------------------------------------------------------------


def test_peel_type_formal_names_simple():
    names = peel_type_formal_names(int_arrow_int)
    assert names == [n]


def test_peel_type_formal_names_multi():
    names = peel_type_formal_names(two_int_arrow_int)
    assert names == [m, n]


def test_peel_type_formal_names_non_arrow():
    names = peel_type_formal_names(t_int)
    assert names == []


# ---------------------------------------------------------------------------
# peel_application_chain
# ---------------------------------------------------------------------------


def test_peel_application_chain_single():
    term = _app(_var(f), _var(x))
    head, args = peel_application_chain(term)
    assert isinstance(head, Var) and head.name == f
    assert len(args) == 1


def test_peel_application_chain_multi():
    # ((f x) y)
    term = _app(_app(_var(f), _var(x)), _var(n))
    head, args = peel_application_chain(term)
    assert isinstance(head, Var) and head.name == f
    assert len(args) == 2


def test_peel_application_chain_no_app():
    term = _var(x)
    head, args = peel_application_chain(term)
    assert head == term
    assert args == []


# ---------------------------------------------------------------------------
# entry_refinement_liquids
# ---------------------------------------------------------------------------


def test_entry_refinements_with_refined_param():
    # (n:{v:Int | v >= 0}) -> Int
    refined = RefinedType(v, t_int, LiquidApp(Name(">=", 0), [LiquidVar(v), LiquidLiteralInt(0)]))
    ty = AbstractionType(n, refined, t_int)
    refs = entry_refinement_liquids(ty, [n], [n])
    assert len(refs) == 1
    # The refinement should be opened with the binder name n
    assert isinstance(refs[0], LiquidApp)


def test_entry_refinements_no_refinement():
    ty = AbstractionType(n, t_int, t_int)
    refs = entry_refinement_liquids(ty, [n], [n])
    assert refs == []


# ---------------------------------------------------------------------------
# collect_recursive_calls_with_paths
# ---------------------------------------------------------------------------


def test_collect_recursive_calls_simple():
    # f = \n. if n == 0 then 1 else f (n - 1)
    body = _if(
        _app(_app(_var(Name("==", 0)), _var(n)), _lit(0)),
        _lit(1),
        _app(_var(f), _app(_app(_var(Name("-", 0)), _var(n)), _lit(1))),
    )
    calls = collect_recursive_calls_with_paths(f, 1, body, None, None, [n], [n])
    assert len(calls) == 1
    call_args, _loc, path, _nested = calls[0]
    assert len(call_args) == 1
    # Should have a path guard (the else branch of the if)
    assert len(path) > 0


def test_collect_recursive_calls_no_recursion():
    body = _app(_app(_var(Name("+", 0)), _var(n)), _lit(1))
    calls = collect_recursive_calls_with_paths(f, 1, body, None, None, [n], [n])
    assert calls == []


def test_collect_recursive_calls_two_branches():
    # f = \m.\n. if m == 0 then ... else (if n == 0 then f (m-1) 1 else f m (n-1))
    body = _if(
        _app(_app(_var(Name("==", 0)), _var(m)), _lit(0)),
        _lit(0),
        _if(
            _app(_app(_var(Name("==", 0)), _var(n)), _lit(0)),
            _app(_app(_var(f), _app(_app(_var(Name("-", 0)), _var(m)), _lit(1))), _lit(1)),
            _app(_app(_var(f), _var(m)), _app(_app(_var(Name("-", 0)), _var(n)), _lit(1))),
        ),
    )
    calls = collect_recursive_calls_with_paths(f, 2, body, None, None, [m, n], [m, n])
    assert len(calls) == 2


# ---------------------------------------------------------------------------
# _lexicographic_less
# ---------------------------------------------------------------------------


def test_lex_less_single_metric():
    call_ms = [LiquidVar(Name("c"))]
    entry_ms = [LiquidVar(Name("e"))]
    result = _lexicographic_less(call_ms, entry_ms)
    # Should be c < e
    assert isinstance(result, LiquidApp)
    assert result.fun == Name("<", 0)


def test_lex_less_two_metrics():
    c0, c1 = LiquidVar(Name("c0")), LiquidVar(Name("c1"))
    e0, e1 = LiquidVar(Name("e0")), LiquidVar(Name("e1"))
    result = _lexicographic_less([c0, c1], [e0, e1])
    # Should be (c0 < e0) || ((c0 == e0) && (c1 < e1))
    assert isinstance(result, LiquidApp)
    assert result.fun == Name("||", 0)


# ---------------------------------------------------------------------------
# _liquefy_metric_at
# ---------------------------------------------------------------------------


def test_liquefy_metric_entry():
    # metric = n, formals = [n]
    metric = _var(n)
    result = _liquefy_metric_at(metric, [n], [n], None)
    assert result is not None
    assert isinstance(result, LiquidVar)


def test_liquefy_metric_at_call():
    # metric = n, call_args = [n - 1]
    metric = _var(n)
    call_arg = _app(_app(_var(Name("-", 0)), _var(n)), _lit(1))
    result = _liquefy_metric_at(metric, [n], [n], [call_arg])
    assert result is not None
    assert isinstance(result, LiquidApp)


# ---------------------------------------------------------------------------
# substitute_formals
# ---------------------------------------------------------------------------


def test_substitute_formals():
    # template: n + 1, formals: [n], args: [Lit(5)]
    template = _app(_app(_var(Name("+", 0)), _var(n)), _lit(1))
    result = substitute_formals(template, [n], [_lit(5)])
    assert isinstance(result, Application)


# ---------------------------------------------------------------------------
# termination_metric_constraints (integration)
# ---------------------------------------------------------------------------


def test_termination_no_metric_returns_true():
    rec = Rec(f, int_arrow_int, _abs(n, _lit(1)), _lit(0), decreasing_by=())
    result = termination_metric_constraints(rec)
    assert isinstance(result, LiquidConstraint)
    assert result.expr == LiquidLiteralBool(True)


def test_termination_factorial_generates_constraints():
    # fact = rec f : (n:Int)->Int = \n. if n==0 then 1 else n * f(n-1) decreasing_by [n]
    body = _if(
        _app(_app(_var(Name("==", 0)), _var(n)), _lit(0)),
        _lit(1),
        _app(
            _app(_var(Name("*", 0)), _var(n)),
            _app(_var(f), _app(_app(_var(Name("-", 0)), _var(n)), _lit(1))),
        ),
    )
    rec = Rec(f, int_arrow_int, _abs(n, body), _lit(0), decreasing_by=(_var(n),))
    result = termination_metric_constraints(rec)
    assert not isinstance(result, type(None))
    assert isinstance(result, LiquidConstraint)


def test_termination_factorial_with_refinement_is_valid():
    """Factorial with n >= 0 precondition should produce valid termination constraints.

    The constraint is wrapped in an Implication to bind `n` in the SMT context,
    since termination constraints are normally conjoined with typing constraints.
    """
    refined_ty = AbstractionType(
        n,
        RefinedType(n, t_int, LiquidApp(Name(">=", 0), [LiquidVar(n), LiquidLiteralInt(0)])),
        t_int,
    )
    body = _if(
        _app(_app(_var(Name("==", 0)), _var(n)), _lit(0)),
        _lit(1),
        _app(
            _app(_var(Name("*", 0)), _var(n)),
            _app(_var(f), _app(_app(_var(Name("-", 0)), _var(n)), _lit(1))),
        ),
    )
    rec = Rec(f, refined_ty, _abs(n, body), _lit(0), decreasing_by=(_var(n),))
    constraint = termination_metric_constraints(rec)
    assert isinstance(constraint, LiquidConstraint)
    # Wrap in Implication to bind n for the SMT solver
    wrapped = Implication(n, t_int, LiquidLiteralBool(True), constraint)
    assert smt_valid(wrapped)


def test_termination_ackermann_generates_conjunction():
    """Ackermann has two recursive calls, so constraints should be a Conjunction."""
    body = _if(
        _app(_app(_var(Name("==", 0)), _var(m)), _lit(0)),
        _app(_app(_var(Name("+", 0)), _var(n)), _lit(1)),
        _if(
            _app(_app(_var(Name("==", 0)), _var(n)), _lit(0)),
            _app(_app(_var(f), _app(_app(_var(Name("-", 0)), _var(m)), _lit(1))), _lit(1)),
            _app(_app(_var(f), _var(m)), _app(_app(_var(Name("-", 0)), _var(n)), _lit(1))),
        ),
    )
    rec = Rec(f, two_int_arrow_int, _abs(m, _abs(n, body)), _lit(0), decreasing_by=(_var(m), _var(n)))
    constraint = termination_metric_constraints(rec)
    assert isinstance(constraint, Conjunction)


def test_termination_ackermann_with_refinements_is_valid():
    """Ackermann with m >= 0 and n >= 0 should produce valid termination constraints."""
    refined_m = RefinedType(m, t_int, LiquidApp(Name(">=", 0), [LiquidVar(m), LiquidLiteralInt(0)]))
    refined_n = RefinedType(n, t_int, LiquidApp(Name(">=", 0), [LiquidVar(n), LiquidLiteralInt(0)]))
    ty = AbstractionType(m, refined_m, AbstractionType(n, refined_n, t_int))
    body = _if(
        _app(_app(_var(Name("==", 0)), _var(m)), _lit(0)),
        _app(_app(_var(Name("+", 0)), _var(n)), _lit(1)),
        _if(
            _app(_app(_var(Name("==", 0)), _var(n)), _lit(0)),
            _app(_app(_var(f), _app(_app(_var(Name("-", 0)), _var(m)), _lit(1))), _lit(1)),
            _app(_app(_var(f), _var(m)), _app(_app(_var(Name("-", 0)), _var(n)), _lit(1))),
        ),
    )
    rec = Rec(f, ty, _abs(m, _abs(n, body)), _lit(0), decreasing_by=(_var(m), _var(n)))
    constraint = termination_metric_constraints(rec)
    assert isinstance(constraint, Conjunction)
    # Wrap in Implications to bind m and n for the SMT solver
    wrapped = Implication(m, t_int, LiquidLiteralBool(True), Implication(n, t_int, LiquidLiteralBool(True), constraint))
    assert smt_valid(wrapped)


def test_termination_mismatched_formals_returns_false():
    """If the number of lambda params doesn't match the type's arity, return False constraint."""
    # Type says 2 params, but body has 1 lambda
    body = _abs(n, _lit(1))
    rec = Rec(f, two_int_arrow_int, body, _lit(0), decreasing_by=(_var(n),))
    constraint = termination_metric_constraints(rec)
    assert isinstance(constraint, LiquidConstraint)
    assert constraint.expr == LiquidLiteralBool(False)
