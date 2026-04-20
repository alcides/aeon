"""Termination metrics (Liquid Haskell-style) for recursive definitions."""

from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidTerm, LiquidVar
from aeon.core.liquid_ops import mk_liquid_and, mk_liquid_or
from aeon.core.substitutions import inline_lets, liquefy, substitution, substitution_in_liquid
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
from aeon.core.types import AbstractionType, RefinedType, Type
from aeon.typechecking.context import TypingContext
from aeon.utils.location import Location
from aeon.utils.name import Name
from aeon.verification.vcs import Conjunction, Constraint, LiquidConstraint

ctrue = LiquidConstraint(LiquidLiteralBool(True))


def peel_abstractions(t: Term) -> tuple[list[Name], Term]:
    names: list[Name] = []
    cur = t
    while isinstance(cur, Abstraction):
        names.append(cur.var_name)
        cur = cur.body
    return names, cur


def peel_type_formal_names(ty: Type) -> list[Name]:
    names: list[Name] = []
    cur: Type = ty
    while isinstance(cur, AbstractionType):
        names.append(cur.var_name)
        cur = cur.type
    return names


def _opened_refinement_liquid(
    var_type: Type, binder_name: Name, term_formals: list[Name], type_formals: list[Name]
) -> LiquidTerm | None:
    match var_type:
        case RefinedType(bname, _bty, ref):
            opened = substitution_in_liquid(ref, LiquidVar(binder_name), bname)
            return align_liquid_to_type_formals(opened, term_formals, type_formals)
        case _:
            return None


def entry_refinement_liquids(
    fn_arrow_type: Type, term_formals: list[Name], type_formals: list[Name]
) -> list[LiquidTerm]:
    """Opened refinement predicates for each curried ``RefinedType`` parameter (entry guards)."""
    out: list[LiquidTerm] = []
    cur: Type = fn_arrow_type
    while isinstance(cur, AbstractionType):
        liq = _opened_refinement_liquid(cur.var_type, cur.var_name, term_formals, type_formals)
        if liq is not None:
            out.append(liq)
        cur = cur.type
    return out


def align_liquid_to_type_formals(liq: LiquidTerm, term_names: list[Name], type_names: list[Name]) -> LiquidTerm:
    """VCs use ``AbstractionType`` binders; liquefy may use distinct ``Name`` ids from lambdas."""
    out = liq
    for t_n, ty_n in zip(term_names, type_names, strict=True):
        if t_n != ty_n:
            out = substitution_in_liquid(out, LiquidVar(ty_n), t_n)
    return out


def peel_application_chain(t: Term) -> tuple[Term, list[Term]]:
    """Left-associate application: ((f x) y) -> f, [x, y]."""
    args: list[Term] = []
    cur = t
    while isinstance(cur, Application):
        args.append(cur.arg)
        cur = cur.fun
    args.reverse()
    return cur, args


def _term_bool_not(cond: Term) -> Term:
    """Surface ``!cond`` as a core application (see parser ``nnot``)."""
    return Application(Var(Name("!", 0), loc=cond.loc), cond, loc=cond.loc)


def _synth_type(ctx: TypingContext, t: Term) -> Type | None:
    """Lazy import: ``typeinfer`` imports this module at load time."""
    try:
        from aeon.typechecking.typeinfer import synth

        return synth(ctx, t)[1]
    except Exception:
        return None


def collect_recursive_calls_with_paths(
    fn: Name,
    arity: int,
    t: Term,
    typing_ctx: TypingContext | None,
    inner_expect_ty: Type | None,
    term_formals: list[Name],
    type_formals: list[Name],
) -> list[tuple[list[Term], Location | None, tuple[Term, ...], tuple[LiquidTerm, ...]]]:
    """Self-calls with ``arity`` args, ``If`` path guards, and nested binder refinements (e.g. match)."""
    found: list[tuple[list[Term], Location | None, tuple[Term, ...], tuple[LiquidTerm, ...]]] = []

    def walk(
        tt: Term,
        path: tuple[Term, ...],
        nested_refs: tuple[LiquidTerm, ...],
        ctx: TypingContext | None,
        expect_ty: Type | None,
    ) -> None:
        match tt:
            case Application(_, _, _):
                head, args = peel_application_chain(tt)
                if isinstance(head, Var) and head.name == fn and len(args) == arity:
                    found.append((args, tt.loc, path, nested_refs))
            case _:
                pass
        match tt:
            case Application(fun, arg, _):
                f_ty = _synth_type(ctx, fun) if ctx is not None else None
                walk(fun, path, nested_refs, ctx, f_ty)
                arg_ty: Type | None = None
                match f_ty:
                    case AbstractionType(_, vt, _):
                        arg_ty = vt
                walk(arg, path, nested_refs, ctx, arg_ty)
            case Abstraction(name, body, _):
                if isinstance(expect_ty, AbstractionType):
                    vty = expect_ty.var_type
                    new_ctx = ctx.with_var(name, vty) if ctx is not None else None
                    ref_l = _opened_refinement_liquid(vty, name, term_formals, type_formals)
                    nrefs = nested_refs + (ref_l,) if ref_l is not None else nested_refs
                    walk(body, path, nrefs, new_ctx, expect_ty.type)
                else:
                    walk(body, path, nested_refs, ctx, None)
            case Let(_, val, body, _):
                walk(val, path, nested_refs, ctx, None)
                walk(body, path, nested_refs, ctx, None)
            case Rec(_, _, val, body, _, _):
                walk(val, path, nested_refs, ctx, None)
                walk(body, path, nested_refs, ctx, None)
            case Annotation(expr, _, _):
                walk(expr, path, nested_refs, ctx, expect_ty)
            case If(cond, then, otherwise, _):
                walk(cond, path, nested_refs, ctx, None)
                walk(then, path + (cond,), nested_refs, ctx, expect_ty)
                walk(otherwise, path + (_term_bool_not(cond),), nested_refs, ctx, expect_ty)
            case TypeApplication(body, _, _):
                walk(body, path, nested_refs, ctx, expect_ty)
            case TypeAbstraction(_, _, body, _):
                walk(body, path, nested_refs, ctx, expect_ty)
            case RefinementApplication(body, refinement, _):
                walk(body, path, nested_refs, ctx, expect_ty)
                walk(refinement, path, nested_refs, ctx, None)
            case RefinementAbstraction(_, _, body, _):
                walk(body, path, nested_refs, ctx, expect_ty)
            case _:
                pass

    walk(t, (), (), typing_ctx, inner_expect_ty)
    return found


def _inner_ctx_and_expect_ty(nrctx: TypingContext, var_type: Type, formals: list[Name]) -> tuple[TypingContext, Type]:
    ctx = nrctx
    cur_ty = var_type
    for nm in formals:
        assert isinstance(cur_ty, AbstractionType)
        ctx = ctx.with_var(nm, cur_ty.var_type)
        cur_ty = cur_ty.type
    return ctx, cur_ty


def _full_path_guard_liquid(
    entry_refs: list[LiquidTerm],
    nested_refs: tuple[LiquidTerm, ...],
    path: tuple[Term, ...],
    formals: list[Name],
    type_formals: list[Name],
) -> LiquidTerm | None:
    parts: list[LiquidTerm] = list(entry_refs) + list(nested_refs)
    if path:
        pl = _liquefy_path_conjuncts(path, formals, type_formals)
        if pl is None:
            return None
        if pl != LiquidLiteralBool(True):
            parts.append(pl)
    if not parts:
        return LiquidLiteralBool(True)
    acc = parts[0]
    for p in parts[1:]:
        acc = mk_liquid_and(acc, p)
    return acc


def _liquefy_path_conjuncts(path: tuple[Term, ...], formals: list[Name], type_formals: list[Name]) -> LiquidTerm | None:
    if not path:
        return LiquidLiteralBool(True)
    parts: list[LiquidTerm] = []
    for g in path:
        liq = liquefy(inline_lets(g))
        if liq is None:
            return None
        parts.append(align_liquid_to_type_formals(liq, formals, type_formals))
    acc = parts[0]
    for p in parts[1:]:
        acc = mk_liquid_and(acc, p)
    return acc


def _metric_call_non_negative(call_ms: list[LiquidTerm]) -> LiquidTerm:
    acc = LiquidApp(Name(">=", 0), [call_ms[0], LiquidLiteralInt(0)])
    for m in call_ms[1:]:
        acc = mk_liquid_and(acc, LiquidApp(Name(">=", 0), [m, LiquidLiteralInt(0)]))
    return acc


def _termination_obligation(
    path: tuple[Term, ...],
    lex: LiquidTerm,
    call_ms: list[LiquidTerm],
    formals: list[Name],
    type_formals: list[Name],
    entry_refs: list[LiquidTerm],
    nested_refs: tuple[LiquidTerm, ...],
) -> Constraint:
    r"""``(entry /\ nested /\ branch) => (lex and metric(call) >= 0)`` when guarded; else ``lex`` only."""
    needs_call_nonneg = bool(path) or bool(entry_refs) or bool(nested_refs)
    oblig = mk_liquid_and(lex, _metric_call_non_negative(call_ms)) if needs_call_nonneg else lex
    full = _full_path_guard_liquid(entry_refs, nested_refs, path, formals, type_formals)
    if full is None:
        return LiquidConstraint(LiquidLiteralBool(False))
    if full == LiquidLiteralBool(True):
        return LiquidConstraint(oblig)
    return LiquidConstraint(LiquidApp(Name("-->", 0), [full, oblig]))


def substitute_formals(template: Term, formals: list[Name], args: list[Term]) -> Term:
    out = template
    for formal, arg in zip(formals, args, strict=True):
        out = substitution(out, arg, formal)
    return out


def _liquefy_metric_at(
    metric: Term,
    formals: list[Name],
    type_formals: list[Name],
    call_args: list[Term] | None,
) -> LiquidTerm | None:
    t = inline_lets(metric)
    if call_args is not None:
        t = substitute_formals(t, formals, [inline_lets(a) for a in call_args])
        t = inline_lets(t)
    liq = liquefy(t)
    if liq is None:
        return None
    return align_liquid_to_type_formals(liq, formals, type_formals)


def _fold_or(terms: list[LiquidTerm]) -> LiquidTerm:
    acc = terms[0]
    for t in terms[1:]:
        acc = mk_liquid_or(acc, t)
    return acc


def _lexicographic_less(call_ms: list[LiquidTerm], entry_ms: list[LiquidTerm]) -> LiquidTerm:
    """Strict lexicographic decrease (Liquid Haskell ``/ [m0, m1, …]``)."""
    assert len(call_ms) == len(entry_ms) and len(call_ms) >= 1
    k = len(call_ms)
    disjuncts: list[LiquidTerm] = []
    for j in range(k):
        step_lt = LiquidApp(Name("<", 0), [call_ms[j], entry_ms[j]])
        if j == 0:
            disjuncts.append(step_lt)
        else:
            prefix = LiquidApp(Name("==", 0), [call_ms[0], entry_ms[0]])
            for i in range(1, j):
                prefix = mk_liquid_and(prefix, LiquidApp(Name("==", 0), [call_ms[i], entry_ms[i]]))
            disjuncts.append(mk_liquid_and(prefix, step_lt))
    return _fold_or(disjuncts)


def termination_metric_constraints(rec: Rec, typing_ctx: TypingContext | None = None) -> Constraint:
    r"""Lexicographic ``m(call) <* m(entry)`` (Liquid Haskell ``/ [m0, m1, …]``).

    With ``typing_ctx`` (the context used to check ``rec.var_value``), also accumulate
    refinements from **nested** abstractions—typically pattern binders after ``match`` lowers
    to an eliminator—so constructor argument refinements guard termination obligations.
    """
    if not rec.decreasing_by:
        return ctrue
    metrics = list(rec.decreasing_by)
    formals, inner = peel_abstractions(rec.var_value)
    type_formals = peel_type_formal_names(rec.var_type)
    if len(type_formals) != len(formals):
        return LiquidConstraint(LiquidLiteralBool(False))
    entry_refs = entry_refinement_liquids(rec.var_type, formals, type_formals)
    # ANF introduces `let anf = …` around sub-expressions; inlining exposes call
    # arguments in terms of parameters so liquefy does not mention ANF temps.
    inner = inline_lets(inner)
    arity = len(formals)
    inner_ctx: TypingContext | None = None
    inner_expect: Type | None = None
    if typing_ctx is not None:
        inner_ctx, inner_expect = _inner_ctx_and_expect_ty(typing_ctx, rec.var_type, formals)
    calls = collect_recursive_calls_with_paths(
        rec.var_name, arity, inner, inner_ctx, inner_expect, formals, type_formals
    )
    if not calls:
        return ctrue

    parts: list[Constraint] = []
    for call_args, _loc, path, nested_refs in calls:
        if len(call_args) != arity:
            parts.append(LiquidConstraint(LiquidLiteralBool(False)))
            continue
        entry_ms: list[LiquidTerm] = []
        call_ms: list[LiquidTerm] = []
        bad = False
        for metric in metrics:
            m_entry = _liquefy_metric_at(metric, formals, type_formals, None)
            m_call = _liquefy_metric_at(metric, formals, type_formals, call_args)
            if m_entry is None or m_call is None:
                bad = True
                break
            entry_ms.append(m_entry)
            call_ms.append(m_call)
        if bad:
            parts.append(LiquidConstraint(LiquidLiteralBool(False)))
            continue
        lex = _lexicographic_less(call_ms, entry_ms)
        parts.append(_termination_obligation(path, lex, call_ms, formals, type_formals, entry_refs, nested_refs))

    if not parts:
        return ctrue
    acc: Constraint = parts[0]
    for p in parts[1:]:
        acc = Conjunction(acc, p)
    return acc
