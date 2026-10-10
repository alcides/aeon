"""Resolve imported names while respecting lexical binding in terms and types."""

from __future__ import annotations

from aeon.errors import NameResolutionError
from aeon.sugar.program import (
    Decorator,
    Definition,
    SAbstraction,
    SAnonConstructor,
    SApplication,
    SAnnotation,
    SIf,
    SQualifiedVar,
    SMethodSelector,
    SRec,
    SLet,
    SMatch,
    SMatchBranch,
    SRefinementAbstraction,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SVar,
    SRefinementApplication,
)
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SRefinementPolymorphism,
    SType,
    STypeConstructor,
    STypePolymorphism,
)
from aeon.utils.name import Name

QualifiedScope = dict[tuple[str, str], Name]
UnqualifiedScope = dict[str, Name]


def resolve_qualified_names_in_sterm(
    t: STerm,
    qualified_scope: QualifiedScope,
    unqualified_scope: UnqualifiedScope,
    constructor_defs: dict[str, Name] | None = None,
    bound: frozenset[str] = frozenset(),
) -> STerm:
    """Replace SQualifiedVar nodes with SVar, and resolve unqualified bare names.

    ``bound`` is the set of names bound by an enclosing binder (function
    parameter, ``let``, ``fun``, ``match`` pattern, ...). A bare variable that
    is locally bound is *never* rewritten to an imported definition — so a
    library's own parameter (e.g. ``NN``'s ``target``) cannot be captured by a
    same-named export of another imported module (e.g. ``Learning.target``).
    Together with the module-prefixing of each library's own top-level
    references, this keeps imported modules from interfering with one another.
    """

    def rec(node: STerm, extra: frozenset[str] = frozenset()) -> STerm:
        return resolve_qualified_names_in_sterm(
            node, qualified_scope, unqualified_scope, constructor_defs, bound | extra
        )

    match t:
        case SAnonConstructor(cname, loc=loc):
            if constructor_defs and cname in constructor_defs:
                return SVar(constructor_defs[cname], loc=loc)
            return t
        case SQualifiedVar(qualifier, name, loc):
            key = (qualifier, name.name)
            if key in qualified_scope:
                return SVar(qualified_scope[key], loc=loc)
            # ``qualifier.name`` where ``qualifier`` names no module or type:
            # treat it as a method call ``qualifier.name`` on a (local)
            # variable ``qualifier`` (issue #27). Since the lexer collapses
            # ``x.m`` into a single QUALIFIED_ID, this is the only place a
            # variable-receiver method call can be recovered. Elaboration
            # resolves it against the receiver's type; if ``qualifier`` is not a
            # bound variable either, it raises there.
            if qualifier not in {q for (q, _) in qualified_scope}:
                # ``n.double.double`` is lexed as one qualified identifier.
                # Recover its receiver recursively so it lowers to
                # ``(.double) ((.double) n)`` rather than looking up a
                # fictional variable named ``n.double``.
                if "." in qualifier:
                    receiver_qualifier, _, receiver_name = qualifier.rpartition(".")
                    receiver = rec(SQualifiedVar(receiver_qualifier, Name(receiver_name), loc=loc))
                else:
                    receiver = SVar(Name(qualifier), loc=loc)
                return SApplication(SMethodSelector(name, loc=loc), receiver, loc=loc)
            raise NameResolutionError(f"Name '{name.name}' not found in module '{qualifier}'", loc)
        case SVar(name, loc) if name.name in unqualified_scope and name.name not in bound:
            resolved = unqualified_scope[name.name]
            if resolved.name.startswith("__ambiguous__"):
                raise NameResolutionError(
                    f"Ambiguous unqualified name '{name.name}'; use a module qualifier or import alias", loc
                )
            return SVar(resolved, loc=loc)
        case SApplication(fun, arg, loc):
            return SApplication(rec(fun), rec(arg), loc=loc)
        case SAbstraction(name, body, loc):
            return SAbstraction(name, rec(body, frozenset({name.name})), loc=loc)
        case SLet(name, val, body, loc):
            # ``val`` is in the outer scope; ``name`` is bound only in ``body``.
            return SLet(name, rec(val), rec(body, frozenset({name.name})), loc=loc, multiplicity=t.multiplicity)
        case SRec(name, ty, val, body, decreasing_by, loc):
            # ``name`` is recursively bound in its own value and the body. Its
            # type ascription can carry refinements that mention imports
            # (``a : {x:_ | Array.size x = 5} := ...``), so resolve it too.
            inner = frozenset({name.name})
            nd = tuple(rec(m, inner) for m in decreasing_by)
            nty = resolve_qualified_names_in_stype(ty, qualified_scope, unqualified_scope, constructor_defs, bound)
            return SRec(
                name, nty, rec(val, inner), rec(body, inner), decreasing_by=nd, loc=loc, multiplicity=t.multiplicity
            )
        case SIf(cond, then, otherwise, loc):
            return SIf(rec(cond), rec(then), rec(otherwise), loc=loc)
        case SAnnotation(expr, ty, loc):
            nty = resolve_qualified_names_in_stype(ty, qualified_scope, unqualified_scope, constructor_defs, bound)
            return SAnnotation(rec(expr), nty, loc=loc)
        case STypeApplication(body, ty, loc):
            return STypeApplication(rec(body), ty, loc=loc)
        case SRefinementApplication(body, refinement, loc):
            return SRefinementApplication(rec(body), rec(refinement), loc=loc)
        case STypeAbstraction(name, kind, body, loc):
            return STypeAbstraction(name, kind, rec(body), loc=loc)
        case SRefinementAbstraction(pname, sort, body, loc):
            return SRefinementAbstraction(pname, sort, rec(body), loc=loc)
        case SMatch(scrutinee, branches, loc):
            return SMatch(
                scrutinee=rec(scrutinee),
                branches=[
                    SMatchBranch(
                        constructor=br.constructor,
                        binders=br.binders,
                        body=rec(br.body, frozenset(b.name for b in br.binders)),
                        qualifier=br.qualifier,
                        loc=br.loc,
                    )
                    for br in branches
                ],
                loc=loc,
            )
        case _:
            return t


def resolve_qualified_names_in_stype(
    ty: SType,
    qualified_scope: QualifiedScope,
    unqualified_scope: UnqualifiedScope,
    constructor_defs: dict[str, Name] | None = None,
    bound: frozenset[str] = frozenset(),
) -> SType:
    """Resolve qualified names inside refinement predicates within types.

    ``bound`` carries the names bound by enclosing refinement binders and
    dependent-function parameters, so a refinement variable (e.g. ``v`` in
    ``{v: T | ...}`` or the ``rows`` parameter of a dependent type) is never
    rewritten to a same-named import.
    """

    def rec_ty(t: SType, extra: frozenset[str] = frozenset()) -> SType:
        return resolve_qualified_names_in_stype(t, qualified_scope, unqualified_scope, constructor_defs, bound | extra)

    def rec_term(t: STerm, extra: frozenset[str] = frozenset()) -> STerm:
        return resolve_qualified_names_in_sterm(t, qualified_scope, unqualified_scope, constructor_defs, bound | extra)

    match ty:
        case SRefinedType(name, inner_ty, refinement, loc):
            # ``name`` is the refinement's self binder, in scope in the predicate.
            return SRefinedType(name, rec_ty(inner_ty), rec_term(refinement, frozenset({name.name})), loc=loc)
        case SAbstractionType(var_name, var_type, body_type, loc):
            # Dependent: ``var_name`` is bound in the codomain.
            return SAbstractionType(
                var_name,
                rec_ty(var_type),
                rec_ty(body_type, frozenset({var_name.name})),
                loc=loc,
                multiplicity=ty.multiplicity,
            )
        case STypePolymorphism(name, kind, body, loc):
            return STypePolymorphism(name, kind, rec_ty(body), loc=loc)
        case SRefinementPolymorphism(name, sort, body, loc):
            return SRefinementPolymorphism(name, rec_ty(sort), rec_ty(body), loc=loc)
        case STypeConstructor(name, args, loc):
            new_args = [rec_ty(a) for a in args]
            return STypeConstructor(name, new_args, loc=loc)
        case _:
            return ty


def resolve_qualified_names_in_definition(
    d: Definition,
    qualified_scope: QualifiedScope,
    unqualified_scope: UnqualifiedScope,
    constructor_defs: dict[str, Name] | None = None,
) -> Definition:
    # The parameters bind names in the body and the return type; an argument
    # type sees the *preceding* parameters (dependent function types). Seeding
    # ``bound`` here is what stops a parameter name from being captured by a
    # same-named import (e.g. ``NN``'s ``target`` vs ``Learning.target``).
    arg_names = frozenset(name.name for name, _ in d.args)
    new_body = resolve_qualified_names_in_sterm(d.body, qualified_scope, unqualified_scope, constructor_defs, arg_names)
    new_args = []
    seen_args: frozenset[str] = frozenset()
    for name, ty in d.args:
        new_args.append(
            (
                name,
                resolve_qualified_names_in_stype(ty, qualified_scope, unqualified_scope, constructor_defs, seen_args),
            )
        )
        seen_args = seen_args | {name.name}
    new_type = (
        resolve_qualified_names_in_stype(d.type, qualified_scope, unqualified_scope, constructor_defs, arg_names)
        if d.type
        else d.type
    )
    new_decorators = [
        Decorator(
            name=dec.name,
            macro_args=[
                resolve_qualified_names_in_sterm(a, qualified_scope, unqualified_scope, constructor_defs)
                for a in dec.macro_args
            ],
            named_args={
                k: resolve_qualified_names_in_sterm(v, qualified_scope, unqualified_scope, constructor_defs)
                for k, v in dec.named_args.items()
            },
            loc=dec.loc,
        )
        for dec in d.decorators
    ]
    # The termination-metric expressions reference the parameters and measures
    # (e.g. ``size xs``) and must be qualified-name-resolved exactly like the
    # body — otherwise a measure name (``size``) is left unresolved and the
    # termination obligation is undischarged. ``arg_names`` is bound so the
    # parameters are not captured by a same-named import.
    new_decreasing = [
        resolve_qualified_names_in_sterm(m, qualified_scope, unqualified_scope, constructor_defs, arg_names)
        for m in d.decreasing_by
    ]
    if (
        new_body is d.body
        and new_args == d.args
        and new_type is d.type
        and new_decorators == d.decorators
        and new_decreasing == list(d.decreasing_by)
    ):
        return d
    return Definition(
        d.name,
        d.foralls,
        new_args,
        new_type,
        new_body,
        new_decorators,
        d.rforalls,
        new_decreasing,
        d.loc,
        arg_multiplicities=d.arg_multiplicities,
        instance_flags=d.instance_flags,
    )
