from dataclasses import dataclass, field
from itertools import combinations
from aeon.core.types import Kind
from aeon.elaboration.context import ElaborationTypingContext
from aeon.elaboration.instantiation import type_substitution
from aeon.facade.api import (
    UnificationFailedError,
    UnificationKindError,
    UnificationSubtypingError,
    UnificationUnknownTypeError,
)
from aeon.sugar.program import (
    SAbstraction,
    SAnonConstructor,
    SAnnotation,
    SApplication,
    SHole,
    SIf,
    SLet,
    SLiteral,
    SRec,
    SRefinementAbstraction,
    SRefinementApplication,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SVar,
)
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    STypeConstructor,
    STypeVar,
    SType,
    STypePolymorphism,
    SRefinementPolymorphism,
    get_type_vars,
)
from aeon.sugar.substitutions import substitute_refinement_param_in_stype, substitution_sterm_in_stype
from aeon.utils.name import Name, fresh_counter
from aeon.sugar.ast_helpers import st_top, st_unit, st_bool


def base(ty: SType) -> SType:
    """Returns the base type of a Refined Type"""
    if isinstance(ty, SRefinedType):
        return ty.type
    return ty


def _extract_base_type_name(ty: SType) -> str | None:
    """Extract the base type constructor name from a type, unwrapping refinements."""
    match ty:
        case STypeConstructor(name, _):
            return name.name
        case SRefinedType(_, inner, _):
            return _extract_base_type_name(inner)
        case _:
            return None


@dataclass
class UnificationVar(SType):
    name: Name
    lower: list[SType] = field(default_factory=list)
    upper: list[SType] = field(default_factory=list)

    def constrain_upper(self, ty):
        bty = base(ty)
        self.upper.append(bty)


@dataclass
class Union(SType):
    united: list[SType]


@dataclass
class Intersection(SType):
    intersected: list[SType]


def elaborate_foralls(e: STerm) -> STerm:
    match e:
        case (
            SLiteral(_, _)
            | SHole(_)
            | SVar(_)
            | SAnnotation(_, _)
            | SAbstraction(_, _)
            | SApplication(_, _)
            | SLet(_, _, _)
            | SIf(_, _, _)
            | STypeApplication(_, _)
            | STypeAbstraction(_, _, _)
            | SRefinementAbstraction(_, _, _)
            | SRefinementApplication(_, _)
        ):
            return e
        case SRec(_, _, _, _, _, loc):
            e1: SRec = e
            if len(get_type_vars(e.var_type)) > 0:
                nt = e.var_type
                nv = e.var_value
                for typevar in get_type_vars(e.var_type):
                    nt = STypePolymorphism(
                        name=typevar.name,
                        kind=Kind.BASE,
                        body=nt,
                    )
                    nv = STypeAbstraction(
                        name=typevar.name,
                        kind=Kind.BASE,
                        body=nv,
                    )

                e1 = SRec(e.var_name, nt, nv, e.body, decreasing_by=e.decreasing_by, loc=loc)
            return e1
        case _:
            assert False, f"Could not elaborate {e} ({type(e)})"


def unify(ctx: ElaborationTypingContext, sub: SType, sup: SType) -> list[SType]:
    match (sub, sup):
        case (_, STypeConstructor(Name("Top", 0))):
            return []
        case (STypeConstructor(subn, subargs), STypeConstructor(supn, supargs)):
            if subn != supn:
                raise UnificationSubtypingError(SHole(Name("todo")), sub, sup)
            elif len(subargs) != len(supargs):
                raise UnificationSubtypingError(SHole(Name("todo")), sub, sup)
            else:
                rt = []
                for subarg, suparg in zip(subargs, supargs):
                    rt += unify(ctx, subarg, suparg)
                return rt
        case (SRefinedType(_, ty, _), _):
            return unify(ctx, ty, sup)
        case (_, SRefinedType(_, ty, _)):
            return unify(ctx, sub, ty)
        case (UnificationVar(_, _, _), _):
            # Skip if this exact bound is already recorded — propagation is
            # idempotent, and re-adding lets two-way ``?X <: ?Y`` / ``?Y <: ?X``
            # cycles diverge through the cross-iteration below.
            if any(u is sup for u in sub.upper):
                return []
            sub.upper.append(sup)
            for l in sub.lower:
                unify(ctx, l, sup)
            return []
        case (_, UnificationVar(_, _, _)):
            if any(s is sub for s in sup.lower):
                return []
            sup.lower.append(sub)
            for u in sup.upper:
                unify(ctx, sub, u)
            return []

        case (STypePolymorphism(name, _, body), _):
            u = UnificationVar(ctx.fresh_typevar())
            nty = type_substitution(sub.body, sub.name, u)
            rt = unify(ctx, nty, sup)
            return [nty] + rt
        case (_, STypePolymorphism(name, _, body)):
            u = UnificationVar(ctx.fresh_typevar())
            unify(ctx, sub, type_substitution(body, name, u))
            return []

        case (SAbstractionType(_, sub_vtype, sub_rtype), SAbstractionType(_, sup_vtype, sup_rtype)):
            unify(ctx, sup_vtype, sub_vtype)
            unify(ctx, sub_rtype, sup_rtype)
            return []

        case (STypeVar(subn), STypeVar(supn)):
            if subn == supn:
                return []
            else:
                raise UnificationSubtypingError(SHole(Name("todo")), sub, sup)

        case (STypeConstructor(name1, args), STypeConstructor(name2, args2)):
            if name1 != name2:
                raise UnificationSubtypingError(SHole(Name("todo")), sub, sup)
            elif len(args) != len(args2):
                raise UnificationSubtypingError(
                    SHole(Name("todo")), sub, sup, msg="Type constructor with different number of arguments."
                )
            else:
                for a1, a2 in zip(args, args2):
                    unify(ctx, a1, a2)
                return []

        case _:
            raise UnificationSubtypingError(SHole(Name("todo")), sub, sup)


def _resolve_uvars(ty: SType) -> SType:
    """Replace every ``UnificationVar`` inside ``ty`` with its first concrete bound.

    Two ``STypeConstructor``s built around different unification variables (each
    pointing at the same concrete type) compare unequal because the variables
    themselves differ. This helper produces a structurally-comparable surface for
    ``unify_single`` so the equality check no longer trips on phantom UVars.
    """
    match ty:
        case UnificationVar(_, lower, upper):
            for cand in lower + upper:
                resolved = _resolve_uvars(cand)
                if not isinstance(resolved, UnificationVar):
                    return resolved
            return ty
        case STypeConstructor(name, args, loc=loc):
            return STypeConstructor(name, [_resolve_uvars(a) for a in args], loc=loc)
        case SRefinedType(name, inner, ref, loc=loc):
            return SRefinedType(name, _resolve_uvars(inner), ref, loc=loc)
        case SAbstractionType(vname, vty, rty, loc=loc):
            return SAbstractionType(vname, _resolve_uvars(vty), _resolve_uvars(rty), loc=loc)
        case STypePolymorphism(name, kind, body, loc=loc):
            return STypePolymorphism(name, kind, _resolve_uvars(body), loc=loc)
        case SRefinementPolymorphism(name, sort, body, loc=loc):
            return SRefinementPolymorphism(name, _resolve_uvars(sort), _resolve_uvars(body), loc=loc)
        case _:
            return ty


def unify_single(vname: str, xs: list[SType]) -> SType:
    match [x for x in xs if x != st_top]:
        case []:
            return st_unit
        case other:
            resolved = [_resolve_uvars(x) for x in other]
            fst_r = resolved[0]
            fst_original = other[0]
            for snd, snd_r in zip(other[1:], resolved[1:]):
                if snd_r != fst_r:
                    raise UnificationFailedError(vname, fst_original, snd)
            return fst_r


def remove_unions_and_intersections(ctx: ElaborationTypingContext, ty: SType) -> SType:
    match ty:
        case Union(united):
            # TODO: raise better errors
            return unify_single("?", united)
        case Intersection(intersected):
            return unify_single("?", intersected)
        case SAbstractionType(name, vtype, rtype, loc):
            return SAbstractionType(
                var_name=name,
                var_type=remove_unions_and_intersections(ctx, vtype),
                type=remove_unions_and_intersections(ctx, rtype),
                loc=loc,
                multiplicity=ty.multiplicity,
            )
        case STypePolymorphism(name, kind, body, loc):
            return STypePolymorphism(
                name=name,
                kind=kind,
                body=remove_unions_and_intersections(
                    ctx,
                    body,
                ),
                loc=loc,
            )
        case SRefinementPolymorphism(name, sort, body, loc):
            return SRefinementPolymorphism(
                name=name,
                sort=remove_unions_and_intersections(ctx, sort),
                body=remove_unions_and_intersections(ctx, body),
                loc=loc,
            )
        case STypeConstructor(name, args, loc):
            return STypeConstructor(name, [remove_unions_and_intersections(ctx, arg) for arg in args], loc=loc)
        case SRefinedType(name, ity, ref, loc):
            innert = remove_unions_and_intersections(ctx, ity)
            return SRefinedType(name=name, type=innert, refinement=ref, loc=loc)
        case _:
            return ty


def wrap_unification(ctx: ElaborationTypingContext, t: STerm, us: list[SType]) -> STerm:
    nt = t
    for u in us:
        nt = STypeApplication(nt, u)
    return nt


def ensure_not_polymorphism(ctx: ElaborationTypingContext, t: STerm, ty: SType) -> tuple[STerm, SType]:
    while isinstance(ty, STypePolymorphism):
        u = UnificationVar(ctx.fresh_typevar())
        ty = type_substitution(ty.body, ty.name, u)
        t = STypeApplication(t, u)
    return t, ty


def elaborate_synth(ctx: ElaborationTypingContext, t: STerm) -> tuple[STerm, SType]:
    match t:
        case SLiteral(_, ty):
            return (t, ty)
        case SVar(name):
            match ctx.type_of(name):
                case None:
                    raise UnificationUnknownTypeError(t)
                case ty:
                    return (t, ty)
        case SAnonConstructor():
            raise UnificationUnknownTypeError(t)
        case SHole(_):
            u = UnificationVar(ctx.fresh_typevar())
            return (t, u)
        case SAnnotation(expr, ty):
            ann = elaborate_check(ctx, expr, ty)
            return (SAnnotation(ann, ty), ty)
        case SAbstraction(name, body):
            u = UnificationVar(ctx.fresh_typevar())
            nctx = ctx.with_var(name, u)
            (t2, bt) = elaborate_synth(nctx, body)
            return (SAbstraction(name, t2), SAbstractionType(name, u, bt))
        case STypeApplication(body, ty):
            (inner, innert) = elaborate_synth(ctx, body)
            assert isinstance(innert, STypePolymorphism)

            u = UnificationVar(ctx.fresh_typevar())
            u.upper.append(ty)
            u.lower.append(ty)

            nty = type_substitution(innert.body, innert.name, u)
            return (STypeApplication(inner, t.type), nty)
        case SRefinementApplication(body, refinement):
            (inner, innert) = elaborate_synth(ctx, body)
            assert isinstance(innert, SRefinementPolymorphism)

            ref_type = SAbstractionType(Name("_", fresh_counter.fresh()), innert.sort, st_bool)
            nrefinement = elaborate_check(ctx, refinement, ref_type)

            nty = substitution_sterm_in_stype(innert.body, nrefinement, innert.name)
            return (SRefinementApplication(inner, nrefinement), nty)

        case SLet(name, value, body):
            u = UnificationVar(ctx.fresh_typevar())
            nval = elaborate_check(ctx, value, u)
            (nbody, nbody_type) = elaborate_synth(ctx.with_var(name, u), body)
            return SLet(name, nval, nbody, multiplicity=t.multiplicity), nbody_type
        case SRec(name, vty, val, body, decreasing_by, loc=loc):
            nctx = ctx.with_var(name, vty)
            nval = elaborate_check(nctx, val, vty)
            (nbody, nbody_type) = elaborate_synth(nctx, body)
            return (
                SRec(name, vty, nval, nbody, decreasing_by=decreasing_by, loc=loc, multiplicity=t.multiplicity),
                nbody_type,
            )
        case SIf(cond, then, otherwise):
            ncond = elaborate_check(ctx, cond, st_bool)
            nthen, nthen_type = elaborate_synth(ctx, then)
            nelse, nelse_type = elaborate_synth(ctx, otherwise)
            u = UnificationVar(ctx.fresh_typevar())
            unify(ctx, nthen_type, u)
            unify(ctx, nelse_type, u)
            return SIf(ncond, nthen, nelse), u
        case SApplication(fun, arg):
            (nfun, nfun_type) = elaborate_synth(ctx, fun)
            while isinstance(nfun_type, STypePolymorphism):
                u = UnificationVar(ctx.fresh_typevar())
                nfun = STypeApplication(nfun, u)
                nfun_type = type_substitution(nfun_type.body, nfun_type.name, u)
            while isinstance(nfun_type, SRefinementPolymorphism):
                h = SHole(Name("_pred", fresh_counter.fresh()), is_implicit_refinement=True)
                nfun = SRefinementApplication(nfun, h)
                nfun_type = substitution_sterm_in_stype(nfun_type.body, h, nfun_type.name)

            match nfun_type:
                case SAbstractionType(_, arg_type, return_type, loc):
                    narg = elaborate_check(ctx, arg, arg_type)
                    # No ANF lift: non-trivial arguments are left in place.
                    # The core typechecker's `synth(Application)` introduces a
                    # Form B existential binder for them (see typeinfer.py),
                    # so there is no need to name the argument here.
                    return SApplication(nfun, narg), return_type
                case _:
                    assert False, f"Expected an abstraction type, but got {nfun_type} for {nfun}."
        case _:
            raise UnificationUnknownTypeError(t)


def elaborate_check(ctx: ElaborationTypingContext, t: STerm, ty: SType) -> STerm:
    match (t, ty):
        case (SAbstraction(name, body, loc=loc), SAbstractionType(aname, aty, rty)):
            nctx = ctx.with_var(name, aty)
            nbody = elaborate_check(nctx, body, substitution_sterm_in_stype(rty, SVar(name), aname))
            return SAbstraction(name, nbody, loc=loc)
        case (SLet(name, val, body, loc=loc), _):
            u = UnificationVar(ctx.fresh_typevar())
            nval = elaborate_check(ctx, val, u)
            nctx = ctx.with_var(name, u)
            nbody = elaborate_check(nctx, body, ty)
            return SLet(name, nval, nbody, loc=loc, multiplicity=t.multiplicity)
        case (SRec(name, vty, val, body, decreasing_by, loc=loc), _):
            nctx = ctx.with_var(name, vty)
            nval = elaborate_check(nctx, val, vty)
            nbody = elaborate_check(nctx, body, ty)
            return SRec(name, vty, nval, nbody, decreasing_by=decreasing_by, loc=loc, multiplicity=t.multiplicity)
        case (SIf(cond, then, otherwise, loc=loc), _):
            ncond = elaborate_check(ctx, cond, st_bool)
            nthen = elaborate_check(ctx, then, ty)
            nelse = elaborate_check(ctx, otherwise, ty)
            return SIf(ncond, nthen, nelse, loc=loc)
        case (STypeAbstraction(name, kind, body, loc=loc), STypePolymorphism(tname, tkind, tbody)):
            if kind != tkind:
                assert UnificationKindError(t, ty, kind, tkind)
            nctx = ctx.with_typevar(name, kind)
            nty = type_substitution(tbody, tname, STypeVar(name))
            nbody = elaborate_check(nctx, body, nty)
            return STypeAbstraction(name, kind, nbody, loc=loc)
        case (SRefinementAbstraction(pname, sort, body, loc=loc), SRefinementPolymorphism(rname, rsort, tbody)):
            unify(ctx, sort, rsort)
            nty = substitute_refinement_param_in_stype(tbody, rname, pname)
            nbody = elaborate_check(ctx, body, nty)
            return SRefinementAbstraction(pname, sort, nbody, loc=loc)
        case (SAbstraction(_, _, loc=loc), SRefinementPolymorphism(rname, rsort, tbody)):
            nbody = elaborate_check(ctx, t, tbody)
            return SRefinementAbstraction(rname, rsort, nbody, loc=loc)
        case (SAnonConstructor(cname, loc=loc), _):
            # Resolve anonymous constructor (.cons) using expected type
            base_name = _extract_base_type_name(ty)
            if base_name is not None and cname in ctx.constructor_to_type and cname in ctx.constructor_defs:
                expected_type_name = ctx.constructor_to_type[cname].name
                if expected_type_name == base_name:
                    resolved = SVar(ctx.constructor_defs[cname], loc=loc)
                    return elaborate_check(ctx, resolved, ty)
            # If we can resolve without type match, still use prefixed name
            if cname in ctx.constructor_defs:
                resolved = SVar(ctx.constructor_defs[cname], loc=loc)
                return elaborate_check(ctx, resolved, ty)
            # Fallback: raise error
            raise UnificationUnknownTypeError(t)
        case (SApplication(fun, arg, loc=loc), _):
            u = UnificationVar(ctx.fresh_typevar())
            nfun = elaborate_check(ctx, fun, SAbstractionType(Name("_", fresh_counter.fresh()), u, ty))
            narg = elaborate_check(ctx, arg, u)
            return SApplication(nfun, narg, loc=loc)
        case _:
            (c, s) = elaborate_synth(ctx, t)
            (c, s) = get_rid_of_polymorphism(ctx, c, s, ty)
            unify(ctx, s, ty)
            return c


def get_rid_of_polymorphism(ctx: ElaborationTypingContext, c: STerm, s: SType, ty: SType) -> tuple[STerm, SType]:
    while isinstance(s, STypePolymorphism) and not isinstance(ty, STypePolymorphism):
        u = UnificationVar(ctx.fresh_typevar())
        c = STypeApplication(c, u)
        s = type_substitution(s.body, s.name, u)
    while isinstance(s, SRefinementPolymorphism) and not isinstance(ty, SRefinementPolymorphism):
        h = SHole(Name("_pred", fresh_counter.fresh()), is_implicit_refinement=True)
        c = SRefinementApplication(c, h)
        s = substitution_sterm_in_stype(s.body, h, s.name)
    return (c, s)


def extract_direction(ty: SType, _seen: set[int] | None = None) -> list[SType]:
    """Collect resolved types reachable from ``ty`` (dropping ``UnificationVar`` shells).

    Returns a list, not a set: nested ``STypeConstructor`` instances may transitively
    contain unhashable ``UnificationVar``s, which makes them unhashable. Duplicates
    are pruned by structural equality. The ``_seen`` set tracks UVar identities to
    break cycles like ``A.upper = [B]; B.upper = [A]``.
    """
    assert isinstance(ty, SType)
    match ty:
        case UnificationVar(_, lower, upper):
            if _seen is None:
                _seen = set()
            if id(ty) in _seen:
                return []
            _seen = _seen | {id(ty)}
            r: list[SType] = []
            for t in lower + upper:
                for sub in extract_direction(t, _seen):
                    if sub not in r:
                        r.append(sub)
            return r
        case _:
            return [ty]


def replace_unification_variables(
    ctx: ElaborationTypingContext, ty: SType
) -> tuple[SType, list[Union], list[Intersection]]:
    """Removes unification variables, and replaces them with either Union or
    Intersection Type.

    This function returns lists of unions of intersections.
    """
    unions: list[Union] = []
    intersections: list[Intersection] = []

    def go(ctx: ElaborationTypingContext, ty: SType, polarity: bool) -> SType:
        """The recursive part of the function."""
        match ty:
            case STypeVar(_):
                return ty
            case SAbstractionType(name, vty, rty, loc=loc):
                return SAbstractionType(
                    name,
                    go(ctx, vty, not polarity),
                    go(ctx, rty, polarity),
                    loc=loc,
                    multiplicity=ty.multiplicity,
                )
            case SRefinedType(name, ity, ref, loc=loc):
                nt = go(ctx, ity, polarity)
                return SRefinedType(name, nt, ref, loc=loc)
            case STypePolymorphism(name, kind, body, loc=loc):
                return STypePolymorphism(name, kind, go(ctx, body, polarity), loc=loc)
            case SRefinementPolymorphism(name, sort, body, loc=loc):
                return SRefinementPolymorphism(name, go(ctx, sort, polarity), go(ctx, body, polarity), loc=loc)
            case STypeConstructor(name, args, loc=loc):
                return STypeConstructor(name, [go(ctx, arg, polarity) for arg in args], loc=loc)

            case UnificationVar(_, _, _):
                return Union(list(extract_direction(ty)))
            case _:
                assert False

    return (go(ctx, ty, True), unions, intersections)


def remove_from_union_and_intersection(
    unions: list[Union],
    intersections: list[Intersection],
    to_be_removed: list[Name],
):
    """Removes all unification vars whose name is in the to_be_removed list."""

    def rem(x: SType) -> bool:
        if isinstance(x, UnificationVar):
            return x.name not in to_be_removed
        else:
            return True

    for i in intersections:
        i.intersected = list(filter(rem, i.intersected))

    for union in unions:
        union.united = list(filter(rem, union.united))


def handle_unification_in_type(ctx: ElaborationTypingContext, ty: SType) -> SType:
    # Source: https://dl.acm.org/doi/pdf/10.1145/3409006
    nt, unions, intersections = replace_unification_variables(ctx, ty)

    # 1. Removal of polar variable
    all_positive = [x.name for u in unions for x in u.united if isinstance(x, UnificationVar)]
    all_negative = [x.name for i in intersections for x in i.intersected if isinstance(x, UnificationVar)]
    to_be_removed = [x for x in all_positive if x not in all_negative] + [
        x for x in all_negative if x not in all_positive
    ]

    # 2. Unification of indistinguishable variables
    for union in unions:
        unifications = [x for x in union.united if isinstance(x, UnificationVar)]
        for a, b in combinations(unifications, 2):
            if all(a in u.united and b in u.united for u in unions):
                to_be_removed.append(max(a.name, b.name))

    for i in intersections:
        unifications = [x for x in i.intersected if isinstance(x, UnificationVar)]
        for a, b in combinations(unifications, 2):
            if all(a in j.intersected and b in j.intersected for j in intersections):
                to_be_removed.append(max(a.name, b.name))

    # 3. Flattening of variable sandwiches
    unifications = [x for union in unions for x in union.united if isinstance(x, UnificationVar)]
    for u in unifications:
        base_types_together_with_u_pos = [
            b for un in unions if u in un.united for b in un.united if not isinstance(b, UnificationVar)
        ]
        base_types_together_with_u_neg = [
            b for i in intersections if u in i.intersected for b in i.intersected if not isinstance(b, UnificationVar)
        ]
        # TODO: I think we need subtyping here.

        if any(bp in base_types_together_with_u_neg for bp in base_types_together_with_u_pos):
            to_be_removed.append(u.name)

    remove_from_union_and_intersection(
        unions,
        intersections,
        to_be_removed,
    )
    return remove_unions_and_intersections(ctx, nt)


def elaborate_remove_unification(ctx: ElaborationTypingContext, t: STerm) -> STerm:
    match t:
        case SLiteral() | SVar() | SHole() | SAnonConstructor():
            return t
        case SAnnotation(expr, ty, loc=loc):
            return SAnnotation(elaborate_remove_unification(ctx, expr), ty, loc=loc)
            # TODO NOW: what about ty?
        case SAbstraction(name, body, loc=loc):
            return SAbstraction(name, elaborate_remove_unification(ctx, body), loc=loc)
        case SLet(name, val, body, loc=loc):
            nctx = ctx.with_var(t.var_name, st_unit)  # TODO poly: Unit??
            return SLet(
                name,
                elaborate_remove_unification(ctx, val),
                elaborate_remove_unification(nctx, body),
                loc=loc,
                multiplicity=t.multiplicity,
            )
        case SRec(name, ty, val, body, decreasing_by, loc=loc):
            nty = handle_unification_in_type(ctx, ty)
            nt = remove_unions_and_intersections(ctx, ty)
            nctx = ctx.with_var(t.var_name, t.var_type)
            return SRec(
                name,
                nty,
                elaborate_remove_unification(nctx, val),
                elaborate_remove_unification(nctx, body),
                decreasing_by=decreasing_by,
                loc=loc,
                multiplicity=t.multiplicity,
            )

        case SIf(cond, then, otherwise, loc=loc):
            return SIf(
                elaborate_remove_unification(ctx, cond),
                elaborate_remove_unification(ctx, then),
                elaborate_remove_unification(ctx, otherwise),
                loc=loc,
            )

        case SApplication(fun, arg, loc=loc):
            return SApplication(elaborate_remove_unification(ctx, fun), elaborate_remove_unification(ctx, arg), loc=loc)

        case STypeAbstraction(name, kind, body, loc=loc):
            nctx = ctx.with_typevar(name, kind)
            return STypeAbstraction(name, kind, elaborate_remove_unification(nctx, body), loc=loc)

        case SRefinementAbstraction(name, sort, body, loc=loc):
            nsort = remove_unions_and_intersections(ctx, sort)
            return SRefinementAbstraction(name, nsort, elaborate_remove_unification(ctx, body), loc=loc)

        case STypeApplication(body, ty, loc=loc):
            # Recursively apply itself.
            body = elaborate_remove_unification(ctx, body)

            nt = handle_unification_in_type(ctx, ty)

            match nt:
                case STypeConstructor(Name("Top", _)):
                    return STypeApplication(body, nt, loc=loc)
                case _:
                    should_be_refined = True
                    match body:
                        case SVar(name):
                            match ctx.type_of(name):
                                case STypePolymorphism(_, Kind.BASE, _):
                                    should_be_refined = False
                    match nt:
                        case STypeConstructor(_) | STypeVar(_) | STypeConstructor(_, _):
                            new_type: SType
                            if should_be_refined:
                                nv = Name("self", fresh_counter.fresh())
                                nh = Name("k", fresh_counter.fresh())
                                # TODO NOW: liquidhornapp
                                # ref = LiquidHornApplication("k", [(LiquidVar(new_var), str(nt))])
                                new_type = SRefinedType(nv, nt, SHole(nh))
                            else:
                                new_type = nt
                            return STypeApplication(body, new_type, loc=loc)
                        case SRefinedType(name, ity, ref):
                            # TODO NOW: liquidhornapp
                            # ref = LiquidHornApplication("k", [(LiquidVar(nt.name), str(nt.type))])
                            nh = Name("k", fresh_counter.fresh())
                            ref = SHole(nh)
                            new_type = SRefinedType(name, ity, ref)
                            return STypeApplication(body, new_type, loc=loc)
                        case SAbstractionType(_, _, _):
                            # AbstractionTypes are not refined
                            return STypeApplication(body, nt, loc=loc)
                        # case TypePolymorphism(name, kind, body_):

                        case _:
                            assert False, f"{nt} ({type(nt)}) not an SType."

        case SRefinementApplication(body, refinement, loc=loc):
            return SRefinementApplication(
                elaborate_remove_unification(ctx, body),
                elaborate_remove_unification(ctx, refinement),
                loc=loc,
            )
        case _:
            assert False, f"{t} ({type(t)}) not an STerm."


def elaborate(ctx: ElaborationTypingContext, e: STerm, expected_type: SType = st_top) -> STerm:
    e2 = elaborate_foralls(e)
    e3 = elaborate_check(ctx, e2, expected_type)
    e4 = elaborate_remove_unification(ctx, e3)
    return e4
