"""Liquid-abduction style guard synthesis: map qualifier atoms to core terms."""

from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidTerm, LiquidVar
from aeon.core.terms import Annotation, Application, Literal, Var
from aeon.core.terms import Term
from aeon.core.types import TypeConstructor, Type, refined_to_unrefined_type, t_bool
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


def _is_int_base(ty: Type) -> bool:
    base = refined_to_unrefined_type(ty)
    return isinstance(base, TypeConstructor) and base.name.name == "Int"


def _relational_ops_in(atoms: frozenset[LiquidTerm]) -> list[Name]:
    """Operators of every relational atom appearing *anywhere* in ``atoms`` --
    including nested under ``&&`` / ``||`` (e.g. the ``<=`` of a sortedness
    invariant ``ilen t = 0 || hd <= imin t``). These are the ``⋆ op ⋆``
    qualifier *templates* of the abducible set Q (Polikarpova et al., PLDI'16
    §2: ``⋆`` is a placeholder instantiated with program variables in scope)."""
    ops: set[Name] = set()

    def walk(t: LiquidTerm) -> None:
        if isinstance(t, LiquidApp):
            if t.fun in _REL:
                ops.add(t.fun)
            for a in t.args:
                walk(a)

    for a in atoms:
        walk(a)
    return sorted(ops, key=lambda n: (n.name, n.id))


def bool_terms_from_qualifier_atoms(
    ctx: TypingContext,
    atoms: frozenset[LiquidTerm],
    *,
    max_terms: int = 48,
) -> list[Term]:
    """Bool-typed core guards drawn from the qualifier set Q.

    Two sources, both Synquid liquid abduction (PLDI'16 §2):
    (a) relational atoms already present in Q whose operands are in scope; and
    (b) *template instantiation* -- each relational operator appearing in Q is a
    ``⋆ op ⋆`` qualifier template, re-instantiated with the program variables in
    scope of matching (``Int``) sort, plus the literals ``0``/``1``. (b) is what
    surfaces a discriminating guard such as ``hd <= p`` whose operands the
    harvested atoms only mention over the datatype's own (out-of-scope) binders.
    It fires only when Q carries a relational template *and* an ``Int`` variable
    is in scope, so non-ordering goals pay nothing, and is bounded by
    ``max_terms``."""
    in_ctx = {n for n, _ in ctx.concrete_vars()}
    out: list[Term] = []
    seen: set[tuple[Name, str, str]] = set()

    def emit(op: Name, lhs: Term, rhs: Term) -> None:
        key = (op, repr(lhs), repr(rhs))
        if key in seen:
            return
        seen.add(key)
        out.append(Annotation(Application(Application(Var(op), lhs), rhs), t_bool))

    # (a) harvested atoms with in-scope operands
    for atom in atoms:
        if len(out) >= max_terms:
            return out
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
        emit(atom.fun, lhs, rhs)

    # (b) template instantiation over in-scope Int variables (+ 0/1)
    ops = _relational_ops_in(atoms)
    int_vars = [Var(n) for n, t in ctx.concrete_vars() if _is_int_base(t)]
    if ops and int_vars:
        operands: list[Term] = int_vars + [Literal(0, _INT), Literal(1, _INT)]
        for op in ops:
            for lhs in operands:
                for rhs in operands:
                    if len(out) >= max_terms:
                        return out
                    if lhs == rhs:
                        continue
                    if isinstance(lhs, Literal) and isinstance(rhs, Literal):
                        continue  # constant guard (e.g. ``0 <= 1``) -- never discriminating
                    emit(op, lhs, rhs)
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


def bool_triple_conjunctions(
    ctx: TypingContext,
    atoms: frozenset[LiquidTerm],
    *,
    max_singles: int = 12,
    max_triples: int = 16,
) -> list[Term]:
    """Ternary ``a && b && c`` over relational singles from ``atoms`` (bounded abduction)."""
    singles = bool_terms_from_qualifier_atoms(ctx, atoms, max_terms=max_singles)
    if len(singles) < 3:
        return []
    and_op = Var(Name("&&", 0))
    out: list[Term] = []
    n = min(len(singles), 6)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                if len(out) >= max_triples:
                    return out
                a = _strip_bool_ann(singles[i])
                b = _strip_bool_ann(singles[j])
                c = _strip_bool_ann(singles[k])
                ab = Application(Application(and_op, a), b)
                inner = Application(Application(and_op, ab), c)
                out.append(Annotation(inner, t_bool))
    return out


def bool_quad_conjunctions(
    ctx: TypingContext,
    atoms: frozenset[LiquidTerm],
    *,
    max_singles: int = 12,
    max_quads: int = 12,
) -> list[Term]:
    """Quaternary ``a && b && c && d`` over relational singles (bounded abduction)."""
    singles = bool_terms_from_qualifier_atoms(ctx, atoms, max_terms=max_singles)
    if len(singles) < 4:
        return []
    and_op = Var(Name("&&", 0))
    out: list[Term] = []
    n = min(len(singles), 5)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                for m in range(k + 1, n):
                    if len(out) >= max_quads:
                        return out
                    a = _strip_bool_ann(singles[i])
                    b = _strip_bool_ann(singles[j])
                    c = _strip_bool_ann(singles[k])
                    d = _strip_bool_ann(singles[m])
                    ab = Application(Application(and_op, a), b)
                    abc = Application(Application(and_op, ab), c)
                    inner = Application(Application(and_op, abc), d)
                    out.append(Annotation(inner, t_bool))
    return out
