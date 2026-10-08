"""Shared constructor evidence for lowered inductive eliminators.

Both match checking and termination checking must use the same constructor
equation.  Keeping it here prevents their ADT semantics from drifting.
"""

from __future__ import annotations

from dataclasses import dataclass

from aeon.core.liquid import LiquidTerm, LiquidVar
from aeon.core.substitutions import substitution_in_liquid, substitution_in_type
from aeon.core.terms import Abstraction, Term, Var
from aeon.core.types import AbstractionType, RefinedType, RefinementPolymorphism, Type, TypePolymorphism
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.verification.sub import ensure_refined


@dataclass(frozen=True)
class MatchBranchEvidence:
    """The body, fields, and specialised constructor result fact of a branch."""

    body: Term
    body_type: Type
    fields: tuple[tuple[Name, Type], ...]
    fact: LiquidTerm


def match_branch_evidence(
    ctx: TypingContext, handler: Term, case_type: Type, tyname: str, case_name: Name, scrut: Var
) -> MatchBranchEvidence | None:
    """Recover the result refinement of a lowered ``T_rec`` handler.

    ``case_succ`` and a constructor ``T_succ`` are aligned by generated name;
    constructor argument names are substituted with the handler's binders and
    the constructor result binder with the matched value.
    """
    suffix = case_name.name[len("case_") :] if case_name.name.startswith("case_") else None
    ctor_type = next((ty for n, ty in ctx.vars() if suffix is not None and n.name == f"{tyname}_{suffix}"), None)
    if ctor_type is None:
        return None
    cur: Type = ctor_type
    while isinstance(cur, (TypePolymorphism, RefinementPolymorphism)):
        cur = cur.body
    ctor_args: list[Name] = []
    while isinstance(cur, AbstractionType):
        ctor_args.append(cur.var_name)
        cur = cur.type
    result = ensure_refined(cur)
    if not isinstance(result, RefinedType):
        return None

    fields: list[tuple[Name, Type]] = []
    mapping: dict[Name, LiquidTerm] = {}
    body = handler
    expected = case_type
    while isinstance(expected, AbstractionType) and isinstance(body, Abstraction):
        field = body.var_name
        fields.append((field, expected.var_type))
        if len(fields) <= len(ctor_args):
            mapping[ctor_args[len(fields) - 1]] = LiquidVar(field)
        expected = substitution_in_type(expected.type, Var(field), expected.var_name)
        body = body.body
    if isinstance(expected, AbstractionType):
        return None

    fact = substitution_in_liquid(result.refinement, LiquidVar(scrut.name), result.name)
    for constructor_name, field_term in mapping.items():
        fact = substitution_in_liquid(fact, field_term, constructor_name)
    return MatchBranchEvidence(body, expected, tuple(fields), fact)
