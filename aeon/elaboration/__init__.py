from dataclasses import dataclass, field
from itertools import combinations
from aeon.core.types import Kind
from aeon.elaboration.context import ElaborationTypingContext
from aeon.elaboration.instantiation import type_substitution
from aeon.facade.api import (
    AeonError,
    InstanceResolutionError,
    MethodResolutionError,
    NonOrderableComparisonError,
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
    SImplicitRefinementHole,
    SInstanceHole,
    SLet,
    SLiteral,
    SMethodSelector,
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
from aeon.sugar.instance_registry import lookup_instance
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


def _receiver_arg_index(fn_type: SType | None, type_name: str) -> int:
    """Index (among *explicit* value parameters) of the first parameter whose
    base type is ``type_name`` — i.e. where a method call's receiver should be
    inserted, Lean-style. Type/refinement-polymorphism binders are peeled and
    instance-implicit parameters are skipped (they are auto-filled). Falls back
    to ``0`` (insert first) when no parameter matches or the type is unknown."""
    idx = 0
    ty = fn_type
    while ty is not None:
        match ty:
            case STypePolymorphism(_, _, body) | SRefinementPolymorphism(_, _, body):
                ty = body
            case SAbstractionType(_, var_type, rtype):
                if ty.is_instance:
                    ty = rtype
                    continue
                if _extract_base_type_name(var_type) == type_name:
                    return idx
                idx += 1
                ty = rtype
            case _:
                break
    return 0


def _method_call_spine(t: STerm) -> tuple[Name, STerm, list[STerm]] | None:
    """If ``t`` is the application spine of a method call, return
    ``(method, receiver, call_args)``; otherwise ``None``.

    ``receiver.method a1 ... an`` parses to nested applications whose innermost
    function is the ``SMethodSelector`` and whose first applied argument is the
    receiver: ``App(... App(App(SMethodSelector(method), receiver), a1) ..., an)``.
    We unwind that into the method name, the receiver, and the remaining call
    arguments ``[a1, ..., an]`` (which may be empty)."""
    args: list[STerm] = []
    cur = t
    while isinstance(cur, SApplication):
        args.insert(0, cur.arg)
        cur = cur.fun
    if isinstance(cur, SMethodSelector) and args:
        return (cur.method, args[0], args[1:])
    return None


def _build_method_call(
    ctx: ElaborationTypingContext, method: Name, receiver: STerm, call_args: list[STerm], loc
) -> STerm:
    """Rewrite a method call ``receiver.method call_args...`` (issue #27) into a
    plain application of the resolved method function with the receiver inserted.

    The qualifier is the receiver's inferred base type. Following Lean, the
    receiver is inserted at the first explicit parameter whose type matches the
    receiver's type — not blindly first — so ``xs.map f`` becomes ``List.map f
    xs`` even though ``List.map``'s list is its second argument. Because we have
    the whole call spine here, the common case is a plain reordered application
    (no lambda); only a *partial* call that omits arguments before the receiver
    position needs eta-expansion.

    The returned term is left *unelaborated* so the caller routes it through
    normal synth/check (handling polymorphism, instance holes and the remaining
    arguments uniformly)."""
    (_, recv_ty) = elaborate_synth(ctx, receiver)
    type_name = _extract_base_type_name(_resolve_uvars(recv_ty))
    if type_name is None:
        raise MethodResolutionError(method.name, None, loc)
    resolved = ctx.resolve_method(method.name, type_name)
    if resolved is None:
        raise MethodResolutionError(method.name, type_name, loc)

    k = _receiver_arg_index(ctx.type_of(resolved), type_name)
    term: STerm = SVar(resolved, loc=loc)
    if k <= len(call_args):
        final_args = call_args[:k] + [receiver] + call_args[k:]
        for a in final_args:
            term = SApplication(term, a, loc=loc)
        return term
    # Partial call: the receiver sits past the supplied arguments, so eta-expand
    # the missing pre-receiver parameters into a lambda.
    fresh = [Name(f"_self{fresh_counter.fresh()}") for _ in range(k - len(call_args))]
    final_args = call_args + [SVar(p, loc=loc) for p in fresh] + [receiver]
    for a in final_args:
        term = SApplication(term, a, loc=loc)
    for p in reversed(fresh):
        term = SAbstraction(p, term, loc=loc)
    return term


# Ordered comparison operators are restricted to ordered base types (issue
# #292). The check runs at elaboration, when each operator's type variable is
# instantiated to a concrete type; comparisons at a bare type variable are left
# to the caller's instantiation site. User-defined orderings go through the
# ``Ord`` typeclass instead of these builtins.
ORDERED_COMPARISON_OPERATORS = {"<", "<=", ">", ">="}
ORDERABLE_TYPES = {"Int", "Float", "String"}


def _check_orderable_comparison(body: STerm, ty: SType, loc) -> None:
    """Reject ordered comparisons at non-ordered concrete types.

    ``body`` is the (resolved) head of a type application; when it is one of the
    ordered comparison operators and ``ty`` is a concrete type constructor that
    is not ``Int``/``Float``/``String``, raise ``NonOrderableComparisonError``.
    Type variables and unresolved types are skipped (nothing concrete to
    reject)."""
    if not isinstance(body, SVar) or body.name.name not in ORDERED_COMPARISON_OPERATORS:
        return
    base_name = _extract_base_type_name(ty)
    if base_name is not None and base_name not in ORDERABLE_TYPES:
        raise NonOrderableComparisonError(body.name.name, base_name, loc)


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


def unify_single(origin: str, xs: list[SType]) -> SType:
    """Collapse a union/intersection of inferred types into a single type.

    All members must already agree (up to unification-variable resolution); if
    two members resolve to incompatible types the collapse is impossible, so we
    raise a ``UnificationFailedError`` naming where the conflict came from (the
    ``origin`` describes the union/intersection being collapsed) and the two
    concrete types that clashed.
    """
    match [x for x in xs if x != st_top]:
        case []:
            return st_unit
        case other:
            resolved = [_resolve_uvars(x) for x in other]
            fst_r = resolved[0]
            fst_original = other[0]
            for snd, snd_r in zip(other[1:], resolved[1:]):
                if snd_r != fst_r:
                    raise UnificationFailedError(origin, fst_original, snd)
            return fst_r


def remove_unions_and_intersections(ctx: ElaborationTypingContext, ty: SType) -> SType:
    match ty:
        case Union(united):
            return unify_single(f"the union type {ty}", united)
        case Intersection(intersected):
            return unify_single(f"the intersection type {ty}", intersected)
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
        case SApplication() if (_spine := _method_call_spine(t)) is not None:
            method, receiver, call_args = _spine
            return elaborate_synth(ctx, _build_method_call(ctx, method, receiver, call_args, t.loc))
        case SMethodSelector(method, loc=loc):
            # A selector only ever appears applied to its receiver; standalone
            # is a parser/internal bug.
            raise MethodResolutionError(method.name, None, loc)
        case SApplication(fun, arg):
            (nfun, nfun_type) = elaborate_synth(ctx, fun)
            while isinstance(nfun_type, STypePolymorphism):
                u = UnificationVar(ctx.fresh_typevar())
                nfun = STypeApplication(nfun, u)
                nfun_type = type_substitution(nfun_type.body, nfun_type.name, u)
            while isinstance(nfun_type, SRefinementPolymorphism):
                h = SImplicitRefinementHole(Name("_pred", fresh_counter.fresh()))
                nfun = SRefinementApplication(nfun, h)
                nfun_type = substitution_sterm_in_stype(nfun_type.body, h, nfun_type.name)

            while isinstance(nfun_type, SAbstractionType) and nfun_type.is_instance:
                hole = SInstanceHole(nfun_type.var_type)
                nfun = SApplication(nfun, hole)
                nfun_type = substitution_sterm_in_stype(nfun_type.type, hole, nfun_type.var_name)

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
        case (SApplication(), _) if (_spine := _method_call_spine(t)) is not None:
            method, receiver, call_args = _spine
            return elaborate_check(ctx, _build_method_call(ctx, method, receiver, call_args, t.loc), ty)
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
        h = SImplicitRefinementHole(Name("_pred", fresh_counter.fresh()))
        c = SRefinementApplication(c, h)
        s = substitution_sterm_in_stype(s.body, h, s.name)
    while (
        isinstance(s, SAbstractionType) and s.is_instance and not (isinstance(ty, SAbstractionType) and ty.is_instance)
    ):
        hole = SInstanceHole(s.var_type)
        c = SApplication(c, hole)
        s = substitution_sterm_in_stype(s.type, hole, s.var_name)
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


def _base_subtype(sub: SType, sup: SType) -> bool:
    """Conservative, purely structural subtyping between *base* surface types.

    Used by the unification-flattening step to decide when a variable sandwich
    ``sub <: u <: sup`` can collapse. It is intentionally syntactic — it never
    invokes the SMT solver — and treats refinements transparently (only the
    underlying base type matters). It is a superset of structural equality, so
    it preserves the previous equality-based behaviour while additionally
    relating any type with ``Top``, equal type variables, and covariant
    constructor arguments.
    """
    # Refinements are transparent: relate the underlying base types.
    if isinstance(sub, SRefinedType):
        return _base_subtype(sub.type, sup)
    if isinstance(sup, SRefinedType):
        return _base_subtype(sub, sup.type)
    match (sub, sup):
        case (_, STypeConstructor(Name("Top", _), _)):
            return True
        case (STypeVar(n1), STypeVar(n2)):
            return n1 == n2
        case (STypeConstructor(n1, args1), STypeConstructor(n2, args2)):
            return n1 == n2 and len(args1) == len(args2) and all(_base_subtype(a1, a2) for a1, a2 in zip(args1, args2))
        case (SAbstractionType(_, v1, r1), SAbstractionType(_, v2, r2)):
            # Functions: contravariant in the argument, covariant in the result.
            return _base_subtype(v2, v1) and _base_subtype(r1, r2)
        case _:
            return sub == sup


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
        # The sandwich ``bp <: u <: bn`` collapses whenever some lower bound is a
        # subtype of some upper bound. Using subtyping (rather than equality)
        # also flattens variables squeezed between distinct-but-compatible types,
        # e.g. ``T`` sandwiched against ``Top``.
        if any(_base_subtype(bp, bn) for bp in base_types_together_with_u_pos for bn in base_types_together_with_u_neg):
            to_be_removed.append(u.name)

    remove_from_union_and_intersection(
        unions,
        intersections,
        to_be_removed,
    )
    return remove_unions_and_intersections(ctx, nt)


def elaborate_remove_unification(ctx: ElaborationTypingContext, t: STerm) -> STerm:
    match t:
        case SLiteral() | SVar() | SHole() | SImplicitRefinementHole() | SAnonConstructor():
            return t
        case SAnnotation(expr, ty, loc=loc):
            # The annotation type is elaborated as well, mirroring ``SRec``: any
            # unification variables/unions/intersections introduced while
            # checking the annotation are resolved here instead of leaking into
            # lowering. For a fully concrete user annotation this is a no-op.
            nty = handle_unification_in_type(ctx, ty)
            return SAnnotation(elaborate_remove_unification(ctx, expr), nty, loc=loc)
        case SAbstraction(name, body, loc=loc):
            return SAbstraction(name, elaborate_remove_unification(ctx, body), loc=loc)
        case SLet(name, val, body, loc=loc):
            nval = elaborate_remove_unification(ctx, val)
            # Bind the let variable to its actual (resolved) type in the body's
            # context instead of a ``Unit`` placeholder. The type is recovered by
            # re-synthesising the bound value and resolving its unification
            # variables. This is best-effort — the value may contain holes or
            # reference locally-bound names this pass does not track — so on
            # failure we fall back to ``Top``: an honest "unknown" type, unlike
            # ``Unit``, which previously claimed a concrete type and could mask
            # type errors when the binding was polymorphic.
            try:
                _, vty = elaborate_synth(ctx, val)
                vty = handle_unification_in_type(ctx, vty)
            except (AeonError, AssertionError):
                vty = st_top
            nctx = ctx.with_var(t.var_name, vty)
            return SLet(
                name,
                nval,
                elaborate_remove_unification(nctx, body),
                loc=loc,
                multiplicity=t.multiplicity,
            )
        case SRec(name, ty, val, body, decreasing_by, loc=loc):
            nty = handle_unification_in_type(ctx, ty)
            nt = remove_unions_and_intersections(ctx, ty)
            nctx = ctx.with_var(t.var_name, t.var_type)
            # Bring any instance-implicit (given) constraints declared by this
            # binding's type into scope for its body, so method calls on the
            # constrained type variable resolve to the local dictionary
            # parameter (e.g. ``[_c : Eq a]`` of a constrained instance dict).
            val_ctx = nctx
            for inst_name, inst_class in _collect_given_instances(t.var_type, val):
                val_ctx = val_ctx.with_instance(inst_name, inst_class)
            return SRec(
                name,
                nty,
                elaborate_remove_unification(val_ctx, val),
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

            # Ordered comparisons (``<``, ``<=``, ``>``, ``>=``) are only defined
            # for ordered types (issue #292); reject e.g. ``Bool < Bool`` here,
            # where the operator's type variable has been resolved to ``nt``.
            _check_orderable_comparison(body, nt, loc)

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
                                # The refinement is a Liquid horn application
                                # ``k(self)``: an unknown predicate over the
                                # refined variable, to be solved by the Horn
                                # solver. At the sugar level it is encoded as the
                                # hole applied to ``self``; ``liquefy_app`` lowers
                                # this to ``LiquidHornApplication(k, ...)``.
                                ref = SApplication(SHole(nh), SVar(nv), loc=loc)
                                new_type = SRefinedType(nv, nt, ref)
                            else:
                                new_type = nt
                            return STypeApplication(body, new_type, loc=loc)
                        case SRefinedType(name, ity, _ref):
                            # Replace the existing refinement with a fresh horn
                            # application ``k(name)`` over the already-bound
                            # variable, lowered to a ``LiquidHornApplication``.
                            nh = Name("k", fresh_counter.fresh())
                            ref = SApplication(SHole(nh), SVar(name), loc=loc)
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
        case SInstanceHole(class_type, loc=loc):
            return _resolve_instance_hole(ctx, handle_unification_in_type(ctx, class_type), loc)
        case _:
            assert False, f"{t} ({type(t)}) not an STerm."


def _match_instance_type(pattern: SType, actual: SType, foralls: set[Name], subst: dict[Name, SType]) -> bool:
    """Structurally match an instance's declared type-argument ``pattern``
    (e.g. ``Box a``) against a concrete ``actual`` (e.g. ``Box Int``), binding
    each ``forall`` variable of the pattern in ``subst``. Refinements on either
    side are transparent for matching purposes — the dictionary is selected by
    the underlying type shape, not its refinement."""
    if isinstance(pattern, SRefinedType):
        return _match_instance_type(pattern.type, actual, foralls, subst)
    if isinstance(actual, SRefinedType):
        return _match_instance_type(pattern, actual.type, foralls, subst)
    match pattern:
        case STypeVar(name) if name in foralls:
            prev = subst.get(name)
            if prev is not None:
                return _extract_base_type_name(prev) == _extract_base_type_name(actual)
            subst[name] = actual
            return True
        case STypeVar(name):
            return isinstance(actual, STypeVar) and actual.name == name
        case STypeConstructor(pname, pargs):
            if not isinstance(actual, STypeConstructor):
                return False
            if pname.name != actual.name.name or len(pargs) != len(actual.args):
                return False
            return all(_match_instance_type(p, a, foralls, subst) for p, a in zip(pargs, actual.args))
        case _:
            return False


def _collect_given_instances(var_type: SType, var_value: STerm) -> list[tuple[Name, SType]]:
    """Peel a binding's type and value in tandem, collecting the
    ``(param_name, class_type)`` of every instance-implicit abstraction
    parameter. These are the lexically-available given constraints inside the
    binding's body (e.g. the ``[_c : Eq a]`` of a constrained instance dict)."""
    out: list[tuple[Name, SType]] = []
    ty: SType = var_type
    val: STerm = var_value
    while True:
        if isinstance(val, STypeAbstraction) and isinstance(ty, STypePolymorphism):
            ty, val = ty.body, val.body
        elif isinstance(val, SRefinementAbstraction) and isinstance(ty, SRefinementPolymorphism):
            ty, val = ty.body, val.body
        elif isinstance(val, SAbstraction) and isinstance(ty, SAbstractionType):
            if ty.is_instance:
                out.append((val.var_name, ty.var_type))
            ty, val = ty.type, val.body
        else:
            break
    return out


def _class_types_match(requested: SType, given: SType) -> bool:
    """Two class-constraint types refer to the same instance when their class
    constructor and (head-level) type arguments coincide. Refinements are
    transparent."""
    if isinstance(requested, SRefinedType):
        return _class_types_match(requested.type, given)
    if isinstance(given, SRefinedType):
        return _class_types_match(requested, given.type)
    match (requested, given):
        case (STypeConstructor(rn, ra), STypeConstructor(gn, ga)):
            if rn.name != gn.name or len(ra) != len(ga):
                return False
            return all(_class_types_match(r, g) for r, g in zip(ra, ga))
        case (STypeVar(rn), STypeVar(gn)):
            return rn == gn
        case _:
            return requested == given


def _resolve_instance_hole(ctx: ElaborationTypingContext, class_type: SType, loc) -> STerm:
    """Replace a resolved instance-class type (e.g. ``Eq Int``) with a reference
    to the generated instance dictionary. ``class_type`` must have its unification
    variables already resolved to concrete head constructors.

    Constrained / polymorphic instances (e.g. ``instance [Eq a] : Eq (Box a)``)
    are resolved by unifying the requested type against the instance's declared
    pattern, applying the recovered type arguments, and recursively resolving
    each constraint to a nested dictionary."""
    # A lexically-available given constraint (e.g. the ``[Eq a]`` parameter of a
    # constrained instance) takes priority over the global registry.
    for inst_name, inst_class in ctx.instances:
        if _class_types_match(class_type, inst_class):
            return SVar(inst_name, loc=loc)
    match class_type:
        case STypeConstructor(class_name, args) if args:
            head = _extract_base_type_name(args[0])
            if head is None:
                raise InstanceResolutionError(class_name.name, None, loc)
            info = lookup_instance(class_name.name, head)
            if info is None:
                raise InstanceResolutionError(class_name.name, head, loc)
            # Monomorphic instances resolve directly to their dictionary variable.
            if not info.foralls and not info.num_constraints:
                return SVar(info.dict_name, loc=loc)
            # Polymorphic / constrained: unify the requested type arguments
            # against the instance's declared pattern to recover the ``forall``
            # bindings.
            foralls = set(info.foralls)
            subst: dict[Name, SType] = {}
            if len(info.type_args) != len(args):
                raise InstanceResolutionError(class_name.name, head, loc)
            for pat, actual in zip(info.type_args, args):
                if not _match_instance_type(pat, actual, foralls, subst):
                    raise InstanceResolutionError(class_name.name, head, loc)
            term: STerm = SVar(info.dict_name, loc=loc)
            # One type application per ``forall`` binder, in declaration order.
            for fa in info.foralls:
                ty_arg = subst.get(fa)
                if ty_arg is None:
                    raise InstanceResolutionError(class_name.name, head, loc)
                term = STypeApplication(term, ty_arg, loc=loc)
            # Resolve each constraint (after substitution) to a nested dictionary
            # and supply it as an instance-implicit argument.
            for c in info.constraints:
                c_inst = c
                for name, ty in subst.items():
                    c_inst = type_substitution(c_inst, name, ty)
                c_dict = _resolve_instance_hole(ctx, c_inst, loc)
                term = SApplication(term, c_dict, loc=loc)
            return term
        case _:
            raise InstanceResolutionError(str(class_type), None, loc)


def elaborate(ctx: ElaborationTypingContext, e: STerm, expected_type: SType = st_top) -> STerm:
    e2 = elaborate_foralls(e)
    e3 = elaborate_check(ctx, e2, expected_type)
    e4 = elaborate_remove_unification(ctx, e3)
    return e4


def _elaborate_check_spine(ctx: ElaborationTypingContext, t: STerm, ty: SType, errors: list[AeonError]) -> STerm:
    """Walk the chain of top-level ``SRec`` definitions, elaborating each
    definition's value in isolation so that a failure in one is recorded and the
    remaining definitions are still elaborated.

    Mirrors the ``SRec`` arm of ``elaborate_check``: the body is checked under a
    context that binds the definition's name to its declared type, so it stays
    in scope even when the value failed to elaborate.
    """
    match t:
        case SRec(name, vty, val, body, decreasing_by, loc=loc):
            nctx = ctx.with_var(name, vty)
            try:
                nval = elaborate_check(nctx, val, vty)
            except AeonError as e:
                errors.append(e)
                nval = val
            nbody = _elaborate_check_spine(nctx, body, ty, errors)
            return SRec(name, vty, nval, nbody, decreasing_by=decreasing_by, loc=loc, multiplicity=t.multiplicity)
        case _:
            try:
                return elaborate_check(ctx, t, ty)
            except AeonError as e:
                errors.append(e)
                return t


def _remove_unification_spine(ctx: ElaborationTypingContext, t: STerm, errors: list[AeonError]) -> STerm:
    """Walk the top-level ``SRec`` spine running ``elaborate_remove_unification``
    per definition, so errors raised in this phase (e.g. instance resolution and
    non-orderable comparison checks) are collected per definition rather than
    aborting the whole program.

    Mirrors the ``SRec`` arm of ``elaborate_remove_unification``.
    """
    match t:
        case SRec(name, ty, val, body, decreasing_by, loc=loc):
            nctx = ctx.with_var(t.var_name, t.var_type)
            try:
                nty = handle_unification_in_type(ctx, ty)
                val_ctx = nctx
                for inst_name, inst_class in _collect_given_instances(t.var_type, val):
                    val_ctx = val_ctx.with_instance(inst_name, inst_class)
                nval = elaborate_remove_unification(val_ctx, val)
            except AeonError as e:
                errors.append(e)
                nty = ty
                nval = val
            nbody = _remove_unification_spine(nctx, body, errors)
            return SRec(name, nty, nval, nbody, decreasing_by=decreasing_by, loc=loc, multiplicity=t.multiplicity)
        case _:
            try:
                return elaborate_remove_unification(ctx, t)
            except AeonError as e:
                errors.append(e)
                return t


def elaborate_collecting_errors(
    ctx: ElaborationTypingContext, e: STerm, expected_type: SType = st_top
) -> tuple[STerm | None, list[AeonError]]:
    """Like :func:`elaborate`, but accumulates one error per top-level
    definition that fails instead of bailing on the first.

    Returns ``(term, [])`` on success, or ``(None, errors)`` when at least one
    definition failed to elaborate.
    """
    e2 = elaborate_foralls(e)
    errors: list[AeonError] = []
    e3 = _elaborate_check_spine(ctx, e2, expected_type, errors)
    if errors:
        return None, errors
    e4 = _remove_unification_spine(ctx, e3, errors)
    if errors:
        return None, errors
    return e4, []
