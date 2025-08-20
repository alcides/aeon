from dataclasses import dataclass, field
from itertools import combinations

# from loguru import logger
from aeon.core.types import BaseKind, StarKind
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
    SAnnotation,
    SApplication,
    SHole,
    SIf,
    SLet,
    SLiteral,
    SRec,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SRefinementApplication,
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
from aeon.sugar.substitutions import substitution_sterm_in_stype
from aeon.utils.name import Name, fresh_counter
from aeon.sugar.ast_helpers import st_top, st_unit, st_bool


def base(ty: SType) -> SType:
    """Returns the base type of a Refined Type"""
    if isinstance(ty, SRefinedType):
        return ty.type
    return ty


@dataclass
class UnificationVar(SType):
    name: Name
    lower: list[SType] = field(default_factory=list)
    upper: list[SType] = field(default_factory=list)

    def constrain_upper(self, ty):
        bty = base(ty)
        self.upper.append(bty)

    def __str__(self) -> str:
        return (
            f"UnificationVar({self.name}, {[lw.__str__() for lw in self.lower]}, {[up.__str__() for up in self.upper]})"
        )


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
        ):
            return e
        case SRec(_, _, _, _):
            e1: SRec = e
            if len(get_type_vars(e.var_type)) > 0:
                nt = e.var_type
                nv = e.var_value
                for typevar in get_type_vars(e.var_type):
                    nt = STypePolymorphism(
                        name=typevar.name,
                        kind=BaseKind(),
                        body=nt,
                    )
                    nv = STypeAbstraction(
                        name=typevar.name,
                        kind=BaseKind(),
                        body=nv,
                    )

                e1 = SRec(e.var_name, nt, nv, e.body)
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
            sub.upper.append(sup)
            for l in sub.lower:
                unify(ctx, l, sup)
            return []
        case (_, UnificationVar(_, _, _)):
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

        case (SRefinementPolymorphism(name, _, body), _):
            u = UnificationVar(ctx.fresh_typevar())
            nty = type_substitution(sub.body, sub.name, u)
            rt = unify(ctx, nty, sup)
            return [nty] + rt
        case (_, SRefinementPolymorphism(name, _, body)):
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


def unify_single(vname: str, xs: list[SType]) -> SType:
    match [x for x in xs if x != st_top]:
        case []:
            return st_unit
        case other:
            fst = other[0]
            for snd in other[1:]:
                if snd != fst:
                    raise UnificationFailedError(vname, fst, snd)
            return fst


def remove_unions_and_intersections(ctx: ElaborationTypingContext, ty: SType) -> SType:
    match ty:
        case Union(united):
            # TODO: raise better errors
            return unify_single("?", united)
        case Intersection(intersected):
            return unify_single("?", intersected)
        case SAbstractionType(name, vtype, rtype):
            return SAbstractionType(
                var_name=name,
                var_type=remove_unions_and_intersections(ctx, vtype),
                type=remove_unions_and_intersections(ctx, rtype),
            )
        case STypePolymorphism(name, kind, body):
            return STypePolymorphism(
                name=name,
                kind=kind,
                body=remove_unions_and_intersections(
                    ctx,
                    body,
                ),
            )
        case STypeConstructor(name, args):
            return STypeConstructor(name, [remove_unions_and_intersections(ctx, arg) for arg in args])
        case SRefinedType(name, ity, ref):
            innert = remove_unions_and_intersections(ctx, ity)
            return SRefinedType(name=name, type=innert, refinement=ref)
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
        case SRefinementApplication(body, ty):
            (inner, innert) = elaborate_synth(ctx, body)
            assert isinstance(innert, SRefinementPolymorphism)

            u = UnificationVar(ctx.fresh_typevar())
            u.upper.append(ty)
            u.lower.append(ty)

            nty = type_substitution(innert.body, innert.name, u)
            return (SRefinementApplication(inner, t.type), nty)
        case SLet(name, value, body):
            u = UnificationVar(ctx.fresh_typevar())
            nval = elaborate_check(ctx, value, u)
            (nbody, nbody_type) = elaborate_synth(ctx.with_var(name, u), body)
            return SLet(name, nval, nbody), nbody_type
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
            while isinstance(nfun_type, STypePolymorphism) or isinstance(nfun_type, SRefinementPolymorphism):
                u = UnificationVar(ctx.fresh_typevar())
                if isinstance(nfun_type, STypePolymorphism):
                    nfun = STypeApplication(nfun, u)
                    nfun_type = type_substitution(nfun_type.body, nfun_type.name, u)
                elif isinstance(nfun_type, SRefinementPolymorphism):
                    nfun = SRefinementApplication(nfun, u)
                    nfun_type = type_substitution(nfun_type.body, nfun_type.name, u)

            match nfun_type:
                case SAbstractionType(_, arg_type, return_type):
                    narg = elaborate_check(ctx, arg, arg_type)
                    match narg:
                        case SLiteral(_) | SVar(_):
                            return SApplication(nfun, narg), return_type
                        case _:
                            nname = Name("_anf", fresh_counter.fresh())
                            return SRec(nname, arg_type, narg, SApplication(nfun, SVar(nname))), return_type
                case _:
                    assert False, f"Expected an abstraction type, but got {nfun_type} for {nfun}."
        case _:
            raise UnificationUnknownTypeError(t)


def elaborate_check(ctx: ElaborationTypingContext, t: STerm, ty: SType) -> STerm:
    # logger.log("AST_INFO", f"Elaborating \n {t} \n with expected type {ty}")
    match (t, ty):
        case (SAbstraction(name, body), SAbstractionType(aname, aty, rty)):
            # logger.log("AST_INFO", f"is simple abstraction")
            nctx = ctx.with_var(name, aty)
            nbody = elaborate_check(nctx, body, substitution_sterm_in_stype(rty, SVar(name), aname))
            return SAbstraction(name, nbody)
        case (SLet(name, val, body), _):
            # logger.log("AST_INFO", f"is let")
            u = UnificationVar(ctx.fresh_typevar())
            nval = elaborate_check(ctx, val, u)
            nctx = ctx.with_var(name, u)
            nbody = elaborate_check(nctx, body, ty)
            return SLet(name, nval, nbody)
        case (SRec(name, vty, val, body), _):
            # logger.log("AST_INFO", f"is rec")
            nctx = ctx.with_var(name, vty)
            nval = elaborate_check(nctx, val, vty)
            nbody = elaborate_check(nctx, body, ty)
            return SRec(name, vty, nval, nbody)
        case (SIf(cond, then, otherwise), _):
            # logger.log("AST_INFO", f"is if")
            ncond = elaborate_check(ctx, cond, st_bool)
            nthen = elaborate_check(ctx, then, ty)
            nelse = elaborate_check(ctx, otherwise, ty)
            return SIf(ncond, nthen, nelse)
        case (STypeAbstraction(name, kind, body), STypePolymorphism(tname, tkind, tbody)):
            # logger.log("AST_INFO", f"is type abstraction")
            if kind != tkind:
                assert UnificationKindError(t, ty, kind, tkind)
            nctx = ctx.with_typevar(name, kind)
            nty = type_substitution(tbody, tname, STypeVar(name))
            nbody = elaborate_check(nctx, body, nty)
            return STypeAbstraction(name, kind, nbody)
        # case (SRefinementAbstraction(name, kind, body), SRefinementPolymorphism(tname, tkind, tbody)):
        #     # logger.log("AST_INFO", f"is refinement abstraction")
        #     if kind != tkind:
        #         assert UnificationKindError(t, ty, kind, tkind)
        #     nctx = ctx.with_typevar(name, kind)
        #     nty = type_substitution(tbody, tname, STypeVar(name))
        #     nbody = elaborate_check(nctx, body, nty)
        #     return SRefinementAbstraction(name, kind, nbody)
        case (SApplication(fun, arg), _):
            # logger.log("AST_INFO", f"is application")
            u = UnificationVar(ctx.fresh_typevar())
            nfun = elaborate_check(ctx, fun, SAbstractionType(Name("_", fresh_counter.fresh()), u, ty))
            narg = elaborate_check(ctx, arg, u)
            return SApplication(nfun, narg)
        case _:
            # logger.log("AST_INFO", f"is term")
            (c, s) = elaborate_synth(ctx, t)
            (c, s) = get_rid_of_polymorphism(ctx, c, s, ty)
            unify(ctx, s, ty)
            return c


def get_rid_of_polymorphism(ctx: ElaborationTypingContext, c: STerm, s: SType, ty: SType) -> tuple[STerm, SType]:
    while (isinstance(s, STypePolymorphism) and not isinstance(ty, STypePolymorphism)) or (
        isinstance(s, SRefinementPolymorphism) and not isinstance(ty, SRefinementPolymorphism)
    ):
        u = UnificationVar(ctx.fresh_typevar())
        match s:
            case STypePolymorphism(_, _, _):
                c = STypeApplication(c, u)
                s = type_substitution(s.body, s.name, u)
            case SRefinementPolymorphism(_, _, _):
                c = SRefinementApplication(c, u)
                s = type_substitution(s.body, s.name, u)
    return (c, s)


def extract_direction(ty: SType) -> set[SType]:
    assert isinstance(ty, SType)
    match ty:
        case UnificationVar(_, lower, upper):
            r: set = set()
            for t in lower + upper:
                r = r.union(extract_direction(t))
            return r
        case _:
            return set([ty])


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
            case SAbstractionType(name, vty, rty):
                return SAbstractionType(
                    name,
                    go(ctx, vty, not polarity),
                    go(ctx, rty, polarity),
                )
            case SRefinedType(name, ity, ref):
                nt = go(ctx, ity, polarity)
                return SRefinedType(name, nt, ref)
            case STypePolymorphism(name, kind, body):
                return STypePolymorphism(
                    name,
                    kind,
                    go(ctx, body, polarity),
                )
            case SRefinementPolymorphism(name, kind, body):
                return SRefinementPolymorphism(
                    name,
                    kind,
                    go(ctx, body, polarity),
                )
            case STypeConstructor(name, args):
                return STypeConstructor(name, [go(ctx, arg, polarity) for arg in args])

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
    # logger.log("AST_INFO", f"Handling unification in type: {ty}")
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
    result: SType = remove_unions_and_intersections(ctx, nt)
    # logger.log("AST_INFO", f"Result of unification handling: {result}")
    return result


def elaborate_remove_unification(ctx: ElaborationTypingContext, t: STerm) -> STerm:
    match t:
        case SLiteral() | SVar() | SHole():
            return t
        case SAnnotation(expr, ty):
            # logger.log("AST_INFO", f"Removing Unification of annotation {expr} with type {ty}")
            return SAnnotation(elaborate_remove_unification(ctx, expr), ty)
            # TODO: NOW: what about ty?
        case SAbstraction(name, body):
            # logger.log("AST_INFO", f"Removing Unification of abstraction {name} with body {body}")
            return SAbstraction(name, elaborate_remove_unification(ctx, body))
        case SLet(name, val, body):
            # logger.log("AST_INFO", f"Removing Unification of let {name} with value {val} and body {body}")
            nctx = ctx.with_var(t.var_name, st_unit)  # TODO: poly: Unit??
            return SLet(name, elaborate_remove_unification(ctx, val), elaborate_remove_unification(nctx, body))
        case SRec(name, ty, val, body):
            # logger.log("AST_INFO", f"Removing Unification of rec {name} with type {ty}, value {val}, and body {body}")
            nty = handle_unification_in_type(ctx, ty)
            nt = remove_unions_and_intersections(ctx, ty)
            nctx = ctx.with_var(t.var_name, t.var_type)
            return SRec(name, nty, elaborate_remove_unification(nctx, val), elaborate_remove_unification(nctx, body))

        case SIf(cond, then, otherwise):
            # logger.log("AST_INFO", f"Removing Unification of if with condition {cond}, then {then}, and otherwise {otherwise}")
            return SIf(
                elaborate_remove_unification(ctx, cond),
                elaborate_remove_unification(ctx, then),
                elaborate_remove_unification(ctx, otherwise),
            )

        case SApplication(fun, arg):
            # logger.log("AST_INFO", f"Removing Unification of application with function {fun} and argument {arg}")
            return SApplication(
                elaborate_remove_unification(ctx, fun),
                elaborate_remove_unification(ctx, arg),
            )

        case STypeAbstraction(name, kind, body):
            # logger.log("AST_INFO", f"Removing Unification of type abstraction {name} with kind {kind} and body {body}")
            nctx = ctx.with_typevar(name, kind)
            return STypeAbstraction(name, kind, elaborate_remove_unification(nctx, body))

        case STypeApplication(body, ty):
            # logger.log("AST_INFO", f"Removing Unification of type application with body {body} and type {ty}")
            # Recursively apply itself.
            body = elaborate_remove_unification(ctx, body)

            nt = handle_unification_in_type(ctx, ty)

            match nt:
                case STypeConstructor(Name("Top", _)):
                    return STypeApplication(body, nt)
                case _:
                    should_be_refined = True
                    match body:
                        case SVar(name):
                            match ctx.type_of(name):
                                case STypePolymorphism(_, BaseKind(), _):
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
                            return STypeApplication(body, new_type)
                        case SRefinedType(name, ity, ref):
                            # TODO NOW: liquidhornapp
                            # ref = LiquidHornApplication("k", [(LiquidVar(nt.name), str(nt.type))])
                            nh = Name("k", fresh_counter.fresh())
                            ref = SHole(nh)
                            new_type = SRefinedType(name, ity, ref)
                            return STypeApplication(body, new_type)
                        case SAbstractionType(_, _, _):
                            # AbstractionTypes are not refined
                            return STypeApplication(body, nt)
                        # case TypePolymorphism(name, kind, body_):

                        case _:
                            assert False, f"{nt} ({type(nt)}) not an SType."
                            return t  # for the pre-commit hook to pass

        case SRefinementApplication(body, ty):
            # logger.log("AST_INFO", f"Removing Unification of refinement application with body {body} and type {ty}")
            # Recursively apply itself.
            body = elaborate_remove_unification(ctx, body)

            nt = handle_unification_in_type(ctx, ty)

            match nt:
                case STypeConstructor(Name("Top", _)):
                    return SRefinementApplication(body, nt)
                case _:
                    should_be_refined = True
                    match body:
                        case SVar(name):
                            match ctx.type_of(name):
                                case SRefinementPolymorphism(_, StarKind(), _):
                                    should_be_refined = False
                    match nt:
                        case STypeConstructor(_) | STypeVar(_) | STypeConstructor(_, _):
                            ref_new_type: SType
                            if should_be_refined:
                                nv = Name("self", fresh_counter.fresh())
                                nh = Name("k", fresh_counter.fresh())
                                # TODO NOW: liquidhornapp
                                # ref = LiquidHornApplication("k", [(LiquidVar(new_var), str(nt))])
                                ref_new_type = SRefinedType(nv, nt, SHole(nh))
                            else:
                                ref_new_type = nt
                            return SRefinementApplication(body, ref_new_type)
                        case SRefinedType(name, ity, ref):
                            # TODO NOW: liquidhornapp
                            # ref = LiquidHornApplication("k", [(LiquidVar(nt.name), str(nt.type))])
                            nh = Name("k", fresh_counter.fresh())
                            ref = SHole(nh)
                            ref_new_type = SRefinedType(name, ity, ref)
                            return SRefinementApplication(body, ref_new_type)
                        case SAbstractionType(_, _, _):
                            # AbstractionTypes are not refined
                            return SRefinementApplication(body, nt)
                        case _:
                            assert False, f"{nt} ({type(nt)}) not an SType."
                            return t  # for the pre-commit hook to pass

        case _:
            assert False, f"{t} ({type(t)}) not an STerm."
            return t  # for the pre-commit hook to pass


def elaborate(ctx: ElaborationTypingContext, e: STerm, expected_type: SType = st_top) -> STerm:
    # logger.log("AST_INFO", f"Elaborating \n {e} \n with expected type {expected_type}")
    e2 = elaborate_foralls(e)
    # logger.log("AST_INFO", f"Elaborated foralls: \n {e2}")
    e3 = elaborate_check(ctx, e2, expected_type)
    # logger.log("AST_INFO", f"Elaborated check: \n {e3}")
    e4 = elaborate_remove_unification(ctx, e3)
    # logger.log("AST_INFO", f"Elaborated remove unification: \n {e4}")
    return e4
