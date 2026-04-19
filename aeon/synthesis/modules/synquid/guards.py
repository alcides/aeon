"""Liquid-abduction style guard synthesis: map qualifier atoms to core terms."""

from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidTerm, LiquidVar
from aeon.core.terms import Annotation, Application, Literal, Var
from aeon.core.terms import Term
from aeon.core.types import TypeConstructor, t_bool
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

_REL = frozenset({Name("<", 0), Name("<=", 0), Name(">", 0), Name(">=", 0), Name("==", 0), Name("!=", 0)})
_INT = TypeConstructor(Name("Int", 0), [])


def _liquid_to_int_term(t: LiquidTerm) -> Term | None:
    match t:
        case LiquidLiteralInt(v):
            return Literal(v, _INT)
        case LiquidVar(n):
            return Var(n)
        case _:
            return None


def bool_terms_from_qualifier_atoms(
    ctx: TypingContext,
    atoms: frozenset[LiquidTerm],
    *,
    max_terms: int = 48,
) -> list[Term]:
    """Turn relational qualifier atoms into Bool-typed core terms using prelude ops."""
    in_ctx = {n for n, _ in ctx.concrete_vars()}
    out: list[Term] = []
    for atom in atoms:
        if len(out) >= max_terms:
            break
        if not isinstance(atom, LiquidApp) or atom.fun not in _REL or len(atom.args) != 2:
            continue
        a0, a1 = atom.args
        lhs = _liquid_to_int_term(a0)
        rhs = _liquid_to_int_term(a1)
        if lhs is None or rhs is None:
            continue
        if isinstance(a0, LiquidVar) and a0.name not in in_ctx:
            continue
        if isinstance(a1, LiquidVar) and a1.name not in in_ctx:
            continue
        op = Var(atom.fun)
        t = Application(Application(op, lhs), rhs)
        out.append(Annotation(t, t_bool))
    return out


def _strip_bool_ann(t: Term) -> Term:
    match t:
        case Annotation(inner, _):
            return inner
        case _:
            return t


def bool_pairwise_conjunctions(
    ctx: TypingContext,
    atoms: frozenset[LiquidTerm],
    *,
    max_singles: int = 12,
    max_pairs: int = 24,
) -> list[Term]:
    """Binary ``&&`` of two relational guards from ``atoms`` (bounded abduction step)."""
    singles = bool_terms_from_qualifier_atoms(ctx, atoms, max_terms=max_singles)
    if len(singles) < 2:
        return []
    and_op = Var(Name("&&", 0))
    out: list[Term] = []
    n = min(len(singles), 8)
    for i in range(n):
        for j in range(i + 1, n):
            if len(out) >= max_pairs:
                return out
            a = _strip_bool_ann(singles[i])
            b = _strip_bool_ann(singles[j])
            inner = Application(Application(and_op, a), b)
            out.append(Annotation(inner, t_bool))
    return out
