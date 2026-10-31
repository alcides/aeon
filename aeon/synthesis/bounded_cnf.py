"""Backend-independent structural contract for bounded Boolean CNF.

Only Boolean parameters, literals, negation, conjunction and disjunction are
accepted. Let aliases are expanded; arbitrary helper calls and conditionals
are never treated as atoms. This checker does not use the solver templates.
"""

from __future__ import annotations

from aeon.core.multiplicity import MOmega
from aeon.core.terms import Abstraction, Annotation, Application, Let, Literal, Rec, Term, TypeApplication, Var
from aeon.core.types import AbstractionType, RefinedType, Type, t_bool
from aeon.decorators.api import Metadata
from aeon.utils.name import Name

LiteralKey = tuple[Name, bool]
Clause = frozenset[LiteralKey]
CNF = tuple[Clause, ...]


class CNFError(ValueError):
    """An expression is outside the declared structural contract."""


class CNFResourceLimit(CNFError):
    """Normalization could not finish within its syntax-size limits."""


def base(ty: Type) -> Type:
    return ty.type if isinstance(ty, RefinedType) else ty


def unannotate(term: Term) -> Term:
    while isinstance(term, (Annotation, TypeApplication)):
        term = term.expr if isinstance(term, Annotation) else term.body
    return term


def application(term: Term) -> tuple[Term, list[Term]]:
    arguments = []
    term = unannotate(term)
    while isinstance(term, Application):
        arguments.append(term.arg)
        term = unannotate(term.fun)
    return term, list(reversed(arguments))


def normalize(term: Term, allowed: set[Name], *, max_nodes: int = 10_000) -> CNF:
    """Flatten/deduplicate CNF; true has 0 clauses, false has 1 empty clause.

    This deliberately does not distribute arbitrary formulas into CNF. Aliases
    capture their defining environment so lexical shadowing is preserved.
    """
    remaining = max_nodes

    def visit(t: Term, env: dict, conjunction: bool, negative: bool = False) -> list[Clause] | Clause | bool:
        nonlocal remaining
        remaining -= 1
        if remaining < 0:
            raise CNFResourceLimit("CNF normalization size limit exhausted")
        t = unannotate(t)
        if isinstance(t, Let):
            if t.multiplicity is not MOmega:
                raise CNFError("CNF requires unrestricted bindings")
            # Even an unused alias must be pure CNF syntax: dropping an opaque
            # or effectful initializer is not a semantics-preserving rewrite.
            visit(t.var_value, env, True)
            return visit(t.body, env | {t.var_name: (t.var_value, env)}, conjunction, negative)
        if isinstance(t, Var) and t.name in env:
            value, captured = env[t.name]
            return visit(value, captured, conjunction, negative)
        head, args = application(t)
        op = head.name.name if isinstance(head, Var) and head.name.id == 0 else None
        if conjunction:
            if op == "&&" and len(args) == 2:
                left = visit(args[0], env, True)
                right = visit(args[1], env, True)
                assert isinstance(left, list) and isinstance(right, list)
                return left + right
            clause = visit(t, env, False)
            assert isinstance(clause, (frozenset, bool))
            return [] if clause is True else [frozenset() if clause is False else clause]
        if op == "||" and len(args) == 2 and not negative:
            left = visit(args[0], env, False)
            right = visit(args[1], env, False)
            assert not isinstance(left, list) and not isinstance(right, list)
            if left is True or right is True:
                return True
            literals = (frozenset() if left is False else left) | (frozenset() if right is False else right)
            return True if any((name, not polarity) in literals for name, polarity in literals) else literals
        if op == "!" and len(args) == 1:
            return visit(args[0], env, False, not negative)
        if isinstance(t, Literal) and t.type == t_bool and type(t.value) is bool:
            return t.value != negative
        if isinstance(t, Var) and t.name in allowed:
            return frozenset({(t.name, not negative)})
        raise CNFError(
            "CNF clauses must contain only Boolean input literals; helper calls and non-CNF syntax are unsupported"
        )

    try:
        clauses = visit(term, {}, True)
    except RecursionError as exc:
        raise CNFResourceLimit("CNF normalization recursion limit exhausted") from exc
    assert isinstance(clauses, list)
    if frozenset() in clauses:
        return (frozenset(),)
    return tuple(sorted(set(clauses), key=lambda c: sorted((n.name, n.id, p) for n, p in c)))


def bounds(metadata: Metadata) -> dict[Name, int]:
    return {
        name: entry["bounded_cnf"]
        for name, entry in metadata.items()
        if isinstance(entry, dict) and "bounded_cnf" in entry
    }


def check_program(program: Term, metadata: Metadata) -> bool:
    """Check the actual completed definitions, including surrounding sketches."""
    pending = bounds(metadata)
    if not pending:
        return True
    try:
        while isinstance(program, (Let, Rec)):
            name = program.var_name
            if name in pending:
                limit = pending.pop(name)
                if type(limit) is not int or limit < 0 or not isinstance(program, Rec):
                    return False
                ty, body = program.var_type, unannotate(program.var_value)
                allowed = set()
                while isinstance(ty, AbstractionType):
                    if (
                        base(ty.var_type) != t_bool
                        or ty.multiplicity is not MOmega
                        or not isinstance(body, Abstraction)
                    ):
                        return False
                    allowed.add(body.var_name)
                    ty, body = ty.type, unannotate(body.body)
                if base(ty) != t_bool or len(normalize(body, allowed)) > limit:
                    return False
            program = program.body
        return not pending
    except CNFError:
        return False
