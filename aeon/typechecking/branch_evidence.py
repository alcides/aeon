"""Shared constructor evidence for lowered inductive eliminators.

Both match checking and termination checking must use the same constructor
equation.  Keeping it here prevents their ADT semantics from drifting.
"""

from __future__ import annotations

from dataclasses import dataclass

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar
from aeon.core.substitutions import substitution_in_liquid, substitution_in_type
from aeon.core.terms import Abstraction, Literal, Term, Var
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypePolymorphism,
    t_bool,
    extract_parts,
)
from aeon.core.liquid_ops import mk_liquid_and
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name, fresh_counter
from aeon.verification.sub import ensure_refined, implication_constraint, sub
from aeon.verification.vcs import Constraint, LiquidConstraint, conjoin


def unconstrained_predicate(sort: Type) -> Abstraction:
    """Forget an erased predicate only in the evidence used to justify it.

    Aeon's datatype representation stores refined type arguments, but has no
    separate slots for abstract relations. Such a relation must be proved from
    constructor/scrutinee facts before a match can assume it in its fields.
    """
    parameters = []
    while isinstance(sort, AbstractionType):
        parameters.append(sort.var_name)
        sort = sort.type
    result: Term = Literal(True, t_bool)
    for parameter in reversed(parameters):
        result = Abstraction(parameter, result)
    assert isinstance(result, Abstraction)
    return result


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
    ctor_entry = next(((n, ty) for n, ty in ctx.vars() if suffix is not None and n.name == f"{tyname}_{suffix}"), None)
    if ctor_entry is None:
        return None
    ctor_name, ctor_type = ctor_entry
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
    # Preserve the exact constructor at the scrutinee's instantiated sort.
    constructor = LiquidApp(ctor_name, [LiquidVar(n) for n, _ in fields]) if fields else LiquidVar(ctor_name)
    fact = LiquidApp(Name("&&", 0), [fact, LiquidApp(Name("==", 0), [LiquidVar(scrut.name), constructor])])
    return MatchBranchEvidence(body, expected, tuple(fields), fact)


def match_refinement_obligation(
    ctx: TypingContext,
    handler: Term,
    safe_case: Type,
    case: Type,
    tyname: str,
    case_name: Name,
    scrut: Var,
) -> Constraint:
    """Require instantiated field predicates to follow from actual match facts.

    The safe case retains the scrutinee's refined type arguments but erases
    abstract relations absent from its representation. In particular, neither
    an inferred false predicate nor an explicit stronger predicate may make a
    branch vacuously correct. Dependent fields share the handler's binders.
    """
    safe = match_branch_evidence(ctx, handler, safe_case, tyname, case_name, scrut)
    wanted = match_branch_evidence(ctx, handler, case, tyname, case_name, scrut)
    if safe is None or wanted is None or len(safe.fields) != len(wanted.fields):
        return LiquidConstraint(LiquidLiteralBool(False))
    field_ctx = ctx
    for name, ty in safe.fields:
        field_ctx = field_ctx.with_var(name, ty)
    constraint: Constraint = LiquidConstraint(LiquidLiteralBool(True))
    for (name, actual), (_, expected) in zip(safe.fields, wanted.fields):
        if not isinstance(actual, AbstractionType):
            binder, base, refinement = extract_parts(actual)
            # The obligation concerns this field, not every inhabitant of its
            # unrefined sort. Its singleton links constructor equations and
            # scrutinee measures to the predicate being inferred.
            equality = LiquidApp(Name("==", 0), [LiquidVar(binder), LiquidVar(name)])
            actual = RefinedType(binder, base, mk_liquid_and(refinement, equality))
        constraint = conjoin(constraint, sub(field_ctx, actual, expected))
    witness = Name("match_fact", fresh_counter.fresh())
    constraint = implication_constraint(witness, RefinedType(witness, t_bool, safe.fact), constraint)
    for name, ty in reversed(safe.fields):
        constraint = implication_constraint(name, ty, constraint)
    return constraint
