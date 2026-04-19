"""Termination metrics (Liquid Haskell-style) for recursive definitions."""

from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar
from aeon.core.types import LiquidHornApplication
from aeon.core.substitutions import inline_lets, liquefy, substitution
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    If,
    Let,
    Rec,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.utils.location import Location
from aeon.utils.name import Name
from aeon.verification.vcs import Conjunction, Constraint, LiquidConstraint

ctrue = LiquidConstraint(LiquidLiteralBool(True))


def _liquid_var_names_only(t: LiquidTerm | None) -> set[str]:
    """Variable names appearing as ``LiquidVar`` (not operator symbols in ``LiquidApp``)."""
    if t is None:
        return set()
    match t:
        case LiquidVar(n):
            return {n.name}
        case LiquidApp(_, args, _):
            return set().union(*(_liquid_var_names_only(a) for a in args))
        case LiquidHornApplication(_, argtypes, _):
            return set().union(*(_liquid_var_names_only(a) for a, _ in argtypes))
        case _:
            return set()


def peel_abstractions(t: Term) -> tuple[list[Name], Term]:
    names: list[Name] = []
    cur = t
    while isinstance(cur, Abstraction):
        names.append(cur.var_name)
        cur = cur.body
    return names, cur


def peel_application_chain(t: Term) -> tuple[Term, list[Term]]:
    """Left-associate application: ((f x) y) -> f, [x, y]."""
    args: list[Term] = []
    cur = t
    while isinstance(cur, Application):
        args.append(cur.arg)
        cur = cur.fun
    args.reverse()
    return cur, args


def collect_recursive_calls(fn: Name, arity: int, t: Term) -> list[tuple[list[Term], Location | None]]:
    """All maximal application chains headed by ``Var(fn)`` with exactly ``arity`` arguments."""
    found: list[tuple[list[Term], Location | None]] = []

    def walk(tt: Term) -> None:
        match tt:
            case Application(_, _, _):
                head, args = peel_application_chain(tt)
                if isinstance(head, Var) and head.name == fn and len(args) == arity:
                    found.append((args, tt.loc))
            case _:
                pass
        match tt:
            case Application(fun, arg, _):
                walk(fun)
                walk(arg)
            case Abstraction(_, body, _):
                walk(body)
            case Let(_, val, body, _):
                walk(val)
                walk(body)
            case Rec(_, _, val, body, _, _):
                walk(val)
                walk(body)
            case Annotation(expr, _, _):
                walk(expr)
            case If(cond, then, otherwise, _):
                walk(cond)
                walk(then)
                walk(otherwise)
            case TypeApplication(body, _, _):
                walk(body)
            case TypeAbstraction(_, _, body, _):
                walk(body)
            case RefinementApplication(body, refinement, _):
                walk(body)
                walk(refinement)
            case RefinementAbstraction(_, _, body, _):
                walk(body)
            case _:
                pass

    walk(t)
    return found


def substitute_formals(template: Term, formals: list[Name], args: list[Term]) -> Term:
    out = template
    for formal, arg in zip(formals, args, strict=True):
        out = substitution(out, arg, formal)
    return out


def termination_metric_constraints(rec: Rec) -> Constraint:
    """For a single Int-valued metric, emit ``m(call) < m(params)`` at each self-call (LH-style)."""
    if not rec.decreasing_by:
        return ctrue
    if len(rec.decreasing_by) != 1:
        return LiquidConstraint(LiquidLiteralBool(False))
    metric = rec.decreasing_by[0]
    formals, inner = peel_abstractions(rec.var_value)
    arity = len(formals)
    calls = collect_recursive_calls(rec.var_name, arity, inner)
    if not calls:
        return ctrue

    parts: list[Constraint] = []
    for call_args, _loc in calls:
        if len(call_args) != arity:
            parts.append(LiquidConstraint(LiquidLiteralBool(False)))
            continue
        m_entry = liquefy(inline_lets(metric))
        m_call = liquefy(inline_lets(substitute_formals(metric, formals, call_args)))
        if m_entry is None or m_call is None:
            parts.append(LiquidConstraint(LiquidLiteralBool(False)))
            continue
        allowed_names = {f.name for f in formals}
        call_vars = _liquid_var_names_only(m_call)
        if not call_vars.issubset(allowed_names):
            # ANF temporaries in call arguments are not yet in VC scope; skip (see driver ANF order).
            continue
        parts.append(LiquidConstraint(LiquidApp(Name("<", 0), [m_call, m_entry])))

    if not parts:
        return ctrue
    acc: Constraint = parts[0]
    for p in parts[1:]:
        acc = Conjunction(acc, p)
    return acc
