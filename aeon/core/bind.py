from typing import MutableSequence
from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidLiteralUnit,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    ImplicitRefinementHole,
    Let,
    Rec,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
    Literal,
)
from aeon.core.types import (
    AbstractionType,
    LiquidHornApplication,
    RefinedType,
    RefinementPolymorphism,
    Top,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
)
from aeon.typechecking.context import (
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    TypingContextEntry,
    UninterpretedBinder,
    VariableBinder,
)
from aeon.utils.name import Name, fresh_counter


RenamingSubstitions = list[tuple[str, Name]]


def get_last_id(x: str, subs: RenamingSubstitions) -> Name | None:
    for sub, v in subs[::-1]:
        if x == sub:
            return v
    return None


def check_name(name: Name, subs: RenamingSubstitions) -> tuple[Name, RenamingSubstitions]:
    if name.id == -1:
        nname = Name(name.name, fresh_counter.fresh())
        return nname, subs + [(name.name, nname)]
    else:
        return name, subs + [(name.name, name)]


def apply_subs_name(subs: RenamingSubstitions, name: Name) -> Name:
    for sub, v in subs[::-1]:
        if sub == name.name:
            return v
    return name


def bind_lq(liq: LiquidTerm, subs: RenamingSubstitions) -> LiquidTerm:
    match liq:
        case (
            LiquidLiteralBool(_)
            | LiquidLiteralInt(_)
            | LiquidLiteralFloat(_)
            | LiquidLiteralString(_)
            | LiquidLiteralUnit()
        ):
            return liq
        case LiquidVar(name, loc):
            return LiquidVar(apply_subs_name(subs, name), loc=loc)
        case LiquidApp(fun, args, loc):
            nfun = apply_subs_name(subs, fun)
            return LiquidApp(nfun, [bind_lq(a, subs) for a in args], loc=loc)
        case LiquidHornApplication(name, argtyps, loc):
            return LiquidHornApplication(apply_subs_name(subs, name), argtyps, loc=loc)
        case _:
            assert False, f"Constructed {liq} ({type(liq)}) not supported."


def bind_ctx(ctx: TypingContext, subs: RenamingSubstitions) -> tuple[TypingContext, RenamingSubstitions]:
    entries: MutableSequence[TypingContextEntry] = []
    subs = []
    for entry in ctx.entries:
        e: TypingContextEntry
        match entry:
            case VariableBinder(name, ty):
                name, subs = check_name(name, subs)
                e = VariableBinder(name, bind_type(ty, subs))
            case UninterpretedBinder(name, ty):
                name, subs = check_name(name, subs)
                nty = bind_type(ty, subs)
                # Polymorphic projections (``forall a, forall b, (this:
                # Pair a b) -> a``) are valid uninterpreted binders too;
                # the SMT layer strips the foralls when emitting the UFD.
                assert isinstance(nty, (AbstractionType, TypePolymorphism, RefinementPolymorphism)), (
                    f"UninterpretedBinder type must be a function (possibly polymorphic), got {nty}"
                )
                e = UninterpretedBinder(name, nty)
            case TypeBinder(name, k):
                name, subs = check_name(name, subs)
                e = TypeBinder(name, k)
            case TypeConstructorBinder(name, args):
                name, subs = check_name(name, subs)
                e = TypeConstructorBinder(name, args)
            case _:
                assert False, f"Unique not supported for {ctx} ({type(ctx)})"
        entries.append(e)
    return TypingContext(entries), subs


def bind_type(ty: Type, subs: RenamingSubstitions) -> Type:
    match ty:
        case Top():
            return Top()
        case TypeVar(name, loc):
            return TypeVar(apply_subs_name(subs, name), loc=loc)
        case TypeConstructor(name, args, loc):
            nargs = [bind_type(aty, subs) for aty in args]
            return TypeConstructor(apply_subs_name(subs, name), nargs, loc=loc)

        case AbstractionType(aname, atype, rtype, loc):
            nname, nsubs = check_name(aname, subs)

            return AbstractionType(
                nname, bind_type(atype, subs), bind_type(rtype, nsubs), loc=loc, multiplicity=ty.multiplicity
            )
        case RefinedType(name, ty, ref, loc):
            nty = bind_type(ty, subs)
            nname, nsubs = check_name(name, subs)
            nref = bind_lq(ref, nsubs)
            assert isinstance(nty, (TypeConstructor, TypeVar))
            return RefinedType(nname, nty, nref, loc=loc)
        case TypePolymorphism(name, kind, body, loc):
            name, subs = check_name(name, subs)
            return TypePolymorphism(name, kind, bind_type(body, subs), loc=loc)
        case RefinementPolymorphism(name, sort, body, loc):
            bound_sort = bind_type(sort, subs)
            nname, nsubs = check_name(name, subs)
            return RefinementPolymorphism(nname, bound_sort, bind_type(body, nsubs), loc=loc)
        case _:
            assert False, f"Unique not supported for {ty} ({type(ty)})"


def bind_term(t: Term, subs: RenamingSubstitions) -> Term:
    match t:
        case Literal(_, _):
            return t
        case Var(name, loc):
            return Var(apply_subs_name(subs, name), loc=loc)
        case Hole(name, loc):
            name, _ = check_name(name, subs)
            return Hole(name, loc=loc)
        case ImplicitRefinementHole(name, loc):
            name, _ = check_name(name, subs)
            return ImplicitRefinementHole(name, loc=loc)
        case Annotation(e, ty, loc):
            return Annotation(bind_term(e, subs), bind_type(ty, subs), loc=loc)
        case Application(e1, e2, loc):
            return Application(bind_term(e1, subs), bind_term(e2, subs), loc=loc)
        case Abstraction(name, body, loc):
            name, subs = check_name(name, subs)
            nbody = bind_term(body, subs)
            return Abstraction(name, nbody, loc=loc)
        case TypeApplication(body, ty, loc):
            return TypeApplication(bind_term(body, subs), bind_type(ty, subs), loc=loc)
        case RefinementApplication(body, refinement, loc):
            return RefinementApplication(bind_term(body, subs), bind_term(refinement, subs), loc=loc)
        case TypeAbstraction(name, kind, body, loc):
            name, subs = check_name(name, subs)
            return TypeAbstraction(name, kind, bind_term(body, subs), loc=loc)
        case RefinementAbstraction(name, sort, body, loc):
            name, subs = check_name(name, subs)
            return RefinementAbstraction(name, bind_type(sort, subs), bind_term(body, subs), loc=loc)
        case If(cond, then, otherwise, loc):
            return If(bind_term(cond, subs), bind_term(then, subs), bind_term(otherwise, subs), loc=loc)
        case Let(name, body, cont, loc):
            name, nsubs = check_name(name, subs)
            return Let(name, bind_term(body, subs), bind_term(cont, nsubs), loc, multiplicity=t.multiplicity)
        case Rec(name, ty, body, cont, decreasing_by, loc):
            name, subs = check_name(name, subs)
            return Rec(
                name,
                bind_type(ty, subs),
                bind_term(body, subs),
                bind_term(cont, subs),
                decreasing_by=tuple(bind_term(m, subs) for m in decreasing_by),
                loc=loc,
                multiplicity=t.multiplicity,
                mutual_group_id=t.mutual_group_id,
            )
        case _:
            assert False, f"Unique not supported for {t} ({type(t)})"


def bind_ids(ctx: TypingContext, t: Term) -> tuple[TypingContext, Term]:
    ctx, subs = bind_ctx(ctx, [])
    return ctx, bind_term(t, subs)


def _peel_formals(value: Term) -> tuple[Name, ...]:
    """Value-parameter names of a (possibly polymorphic) definition body — i.e.
    the lambda binders its ``decreasing_by`` metrics refer to."""
    cur = value
    while isinstance(cur, (TypeAbstraction, RefinementAbstraction)):
        cur = cur.body
    formals: list[Name] = []
    while isinstance(cur, Abstraction):
        formals.append(cur.var_name)
        cur = cur.body
    return tuple(formals)


def populate_mutual_companions(t: Term) -> Term:
    """Fill each ``mutual``-group ``Rec``'s ``companions`` with the (now fully
    bound) signatures of its siblings. Run after :func:`bind_ids`. Mutual groups
    are always contiguous on the top-level ``Rec`` spine."""
    from aeon.core.terms import MutualCompanion

    spine: list[Rec] = []
    cur: Term = t
    groups: dict[int, list[MutualCompanion]] = {}
    while isinstance(cur, Rec):
        spine.append(cur)
        if cur.mutual_group_id is not None:
            groups.setdefault(cur.mutual_group_id, []).append(
                MutualCompanion(
                    cur.var_name, cur.var_type, cur.decreasing_by, _peel_formals(cur.var_value), cur.var_value
                )
            )
        cur = cur.body
    if not groups:
        return t
    rebuilt: Term = cur
    for rec in reversed(spine):
        if rec.mutual_group_id is not None:
            comps = tuple(c for c in groups[rec.mutual_group_id] if c.name != rec.var_name)
            rebuilt = Rec(
                rec.var_name,
                rec.var_type,
                rec.var_value,
                rebuilt,
                decreasing_by=rec.decreasing_by,
                loc=rec.loc,
                multiplicity=rec.multiplicity,
                mutual_group_id=rec.mutual_group_id,
                companions=comps,
            )
        else:
            rebuilt = Rec(
                rec.var_name,
                rec.var_type,
                rec.var_value,
                rebuilt,
                decreasing_by=rec.decreasing_by,
                loc=rec.loc,
                multiplicity=rec.multiplicity,
                mutual_group_id=rec.mutual_group_id,
                companions=rec.companions,
            )
    return rebuilt
