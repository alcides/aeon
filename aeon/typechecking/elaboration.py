from __future__ import annotations

from dataclasses import dataclass
from dataclasses import field
from functools import reduce
from itertools import combinations

from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidHornApplication
from aeon.core.liquid import LiquidVar
from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import TypeAbstraction
from aeon.core.terms import TypeApplication
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, base
from aeon.core.types import BaseKind
from aeon.core.types import BaseType
from aeon.core.types import Bottom
from aeon.core.types import bottom
from aeon.core.types import get_type_vars
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import Top
from aeon.core.types import top
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import TypingContext


def elaborate_foralls(e: Term) -> Term:
    if isinstance(e, Literal):
        return e
    elif isinstance(e, Hole):
        return e
    elif isinstance(e, Var):
        return e
    elif isinstance(e, Annotation):
        return e
    elif isinstance(e, Application):
        return e
    elif isinstance(e, Abstraction):
        return e
    elif isinstance(e, Let):
        return e
    elif isinstance(e, Rec):
        e1: Rec = e
        if len(get_type_vars(e.var_type)) > 0:
            nt = e.var_type
            nv = e.var_value
            for typevar in get_type_vars(e.var_type):
                nt = TypePolymorphism(
                    name=typevar.name,
                    kind=BaseKind(),
                    body=nt,
                )
                nv = TypeAbstraction(
                    name=typevar.name,
                    kind=BaseKind(),
                    body=nv,
                )

            e1 = Rec(e.var_name, nt, nv, e.body)

        return e1
    elif isinstance(e, If):
        return e
    elif isinstance(e, TypeApplication):
        return e
    elif isinstance(e, TypeAbstraction):
        return e
    else:
        raise NotImplementedError()


class UnificationException(Exception):
    pass


@dataclass
class UnificationVar(Type):
    name: str
    lower: list[Type] = field(default_factory=list)
    upper: list[Type] = field(default_factory=list)

    def constrain_upper(self, ty):
        bty = base(ty)
        self.upper.append(bty)


def unify(ctx: TypingContext, sub: Type, sup: Type) -> list[Type]:
    if isinstance(sub, Bottom):
        return []
    elif isinstance(sup, Top):
        return []
    elif isinstance(sub, BaseType) and isinstance(sup, BaseType):
        if sub != sup:
            raise UnificationException(f"Found {sub}, but expected {sup}")
        return []
    elif isinstance(sub, RefinedType):
        return unify(ctx, sub.type, sup)
    elif isinstance(sup, RefinedType):
        return unify(ctx, sub, sup.type)
    elif isinstance(sub, UnificationVar):
        sub.upper.append(sup)
        for l in sub.lower:
            unify(ctx, l, sup)
        return []

    elif isinstance(sup, UnificationVar):
        sup.lower.append(sub)
        for u in sup.upper:
            unify(ctx, sub, u)
        return []

    elif isinstance(sup, TypePolymorphism):
        u = UnificationVar(ctx.fresh_var())
        unify(ctx, sub, type_substitution(sup.body, sup.name, u))
        return []

    elif isinstance(sub, TypePolymorphism):
        u = UnificationVar(ctx.fresh_var())
        nty = type_substitution(sub.body, sub.name, u)
        rt = unify(ctx, nty, sup)
        return [nty] + rt

    elif isinstance(sub, AbstractionType) and isinstance(sup, AbstractionType):
        unify(ctx, sup.var_type, sub.var_type)
        unify(ctx, sub.type, sup.type)
        return []
    elif (
        isinstance(sub, TypeVar)
        and isinstance(
            sup,
            TypeVar,
        )
        and sup.name == sup.name
    ):
        return []
    else:
        raise UnificationException(
            f"Failed to unify {sub} with {sup} ({type(sup)})",
        )


def simple_subtype(ctx: TypingContext, a: Type, b: Type):
    """Returns whether a <: b, in the HM typesystem."""
    # TODO: missing proper subtyping
    if isinstance(b, Top):
        return True
    elif isinstance(a, Bottom):
        return True
    else:
        return a == b


def type_lub(ctx: TypingContext, u: Type, t: Type):
    """Returns the smallest of two types."""
    if simple_subtype(ctx, u, t):
        return u
    else:
        return t


def type_glb(ctx: TypingContext, u: Type, t: Type):
    """Returns the largest of two types."""
    if simple_subtype(ctx, u, t):
        return t
    else:
        return u


def remove_unions_and_intersections(ctx: TypingContext, ty: Type) -> Type:
    if isinstance(ty, Union):
        return reduce(lambda a, b: type_lub(ctx, a, b), ty.united, top)
    elif isinstance(ty, Intersection):
        return reduce(lambda a, b: type_glb(ctx, a, b), ty.intersected, bottom)
    elif isinstance(ty, AbstractionType):
        return AbstractionType(
            var_name=ty.var_name,
            var_type=remove_unions_and_intersections(ctx, ty.var_type),
            type=remove_unions_and_intersections(ctx, ty.type),
        )
    elif isinstance(ty, TypePolymorphism):
        return TypePolymorphism(
            name=ty.name,
            kind=ty.kind,
            body=remove_unions_and_intersections(
                ctx,
                ty.body,
            ),
        )
    elif isinstance(ty, RefinedType):
        innert = remove_unions_and_intersections(ctx, ty.type)
        assert isinstance(innert, BaseType) or isinstance(innert, TypeVar)
        return RefinedType(name=ty.name, type=innert, refinement=ty.refinement)
    else:
        return ty


def wrap_unification(ctx: TypingContext, t: Term, us: list[Type]) -> Term:
    nt = t
    for u in us:
        nt = TypeApplication(nt, u)
    return nt


def ensure_not_polymorphism(ctx: TypingContext, t: Term, ty: Type) -> tuple[Term, Type]:
    while isinstance(ty, TypePolymorphism):
        u = UnificationVar(ctx.fresh_var())
        ty = type_substitution(ty.body, ty.name, u)
        t = TypeApplication(t, u)
    return t, ty


def elaborate_synth(ctx: TypingContext, t: Term) -> tuple[Term, Type]:
    if isinstance(t, Literal):
        return t, t.type

    elif isinstance(t, Var):
        x: Type | None = ctx.type_of(t.name)
        if x is None:
            raise UnificationException(f"Undefined variable {t}")
        return (t, x)

    elif isinstance(t, Hole):
        u = UnificationVar(ctx.fresh_var())
        return (t, u)

    elif isinstance(t, Annotation):
        ann = elaborate_check(ctx, t.expr, t.type)
        return (Annotation(ann, t.type), t.type)

    elif isinstance(t, Abstraction):
        u = UnificationVar(ctx.fresh_var())
        nctx = ctx.with_var(t.var_name, u)
        (b, bt) = elaborate_synth(nctx, t.body)
        return (t, AbstractionType(t.var_name, u, bt))

    elif isinstance(t, TypeApplication):
        (inner, innert) = elaborate_synth(ctx, t.body)
        assert isinstance(innert, TypePolymorphism)

        u = UnificationVar(ctx.fresh_var())
        u.upper.append(t.type)
        u.lower.append(t.type)

        nty = type_substitution(innert.body, innert.name, u)
        return (TypeApplication(inner, t.type), nty)
    elif isinstance(t, Let):
        u = UnificationVar(ctx.fresh_var())
        nval = elaborate_check(ctx, t.var_value, u)
        (nbody, nbody_type) = elaborate_synth(
            ctx.with_var(t.var_name, u),
            t.body,
        )
        return Let(t.var_name, nval, nbody), nbody_type
    elif isinstance(t, If):
        ncond = elaborate_check(ctx, t.cond, t_bool)
        nthen, nthen_type = elaborate_synth(ctx, t.then)
        nelse, nelse_type = elaborate_synth(ctx, t.otherwise)
        u = UnificationVar(ctx.fresh_var())
        unify(ctx, nthen_type, u)
        unify(ctx, nelse_type, u)
        return If(ncond, nthen, nelse), u
    else:
        raise UnificationException(f"Could not infer the type of {t}")


def elaborate_check(ctx: TypingContext, t: Term, ty: Type) -> Term:
    if isinstance(t, Abstraction) and isinstance(ty, AbstractionType):
        # substitute name of argument in type?
        nbody = elaborate_check(
            ctx.with_var(t.var_name, ty.var_type),
            t.body,
            ty.type,
        )
        return Abstraction(t.var_name, nbody)

    elif isinstance(t, Let):
        u = UnificationVar(ctx.fresh_var())
        nval = elaborate_check(ctx, t.var_value, u)
        nbody = elaborate_check(
            ctx.with_var(t.var_name, u),
            t.body,
            ty,
        )
        return Let(t.var_name, nval, nbody)

    elif isinstance(t, Rec):
        nctx = ctx.with_var(t.var_name, t.var_type)
        nval = elaborate_check(nctx, t.var_value, t.var_type)
        nbody = elaborate_check(
            nctx,
            t.body,
            ty,
        )

        return Rec(t.var_name, t.var_type, nval, nbody)

    elif isinstance(t, If):
        ncond = elaborate_check(ctx, t.cond, t_bool)
        nthen = elaborate_check(ctx, t.then, ty)
        nelse = elaborate_check(ctx, t.otherwise, ty)
        return If(ncond, nthen, nelse)

    elif isinstance(t, TypeAbstraction) and isinstance(ty, TypePolymorphism):
        if t.kind != ty.kind:
            assert UnificationException(
                f"Failed to unify the kind of {t} with kind of type {ty}",
            )
        nctx = ctx.with_typevar(t.name, t.kind)
        nty = type_substitution(ty.body, ty.name, TypeVar(t.name))
        nbody = elaborate_check(nctx, t.body, nty)
        return TypeAbstraction(t.name, t.kind, nbody)

    elif isinstance(t, Application):
        u = UnificationVar(ctx.fresh_var())
        nfun = elaborate_check(ctx, t.fun, AbstractionType("_", u, ty))
        narg = elaborate_check(ctx, t.arg, u)
        return Application(nfun, narg)

    else:
        (c, s) = elaborate_synth(ctx, t)
        if isinstance(s, TypePolymorphism) and not isinstance(ty, TypePolymorphism):
            u = UnificationVar(ctx.fresh_var())
            c = TypeApplication(c, u)
            s = type_substitution(s.body, s.name, u)
        unify(ctx, s, ty)
        return c


@dataclass
class Union(Type):
    united: list[Type]


@dataclass
class Intersection(Type):
    intersected: list[Type]


def extract_direction(ty: Type, upper: bool = True) -> set[Type]:
    if isinstance(ty, UnificationVar):
        f: set[Type] = set()
        candidates = ty.upper if upper else ty.lower
        for u in candidates:
            f = f.union(extract_direction(u, upper))
        return f
    else:
        base = top if upper else bottom
        return {ty, base}


def replace_unification_variables(
    ctx: TypingContext,
    ty: Type,
) -> tuple[Type, list[Union], list[Intersection]]:
    """Removes unification variables, and replaces them with either Union or
    Intersection Type.

    This function returns lists of unions of intersections.
    """
    unions: list[Union] = []
    intersections: list[Intersection] = []

    def go(ctx: TypingContext, ty: Type, polarity: bool) -> Type:
        """The recursive part of the function."""
        if isinstance(ty, BaseType):
            return ty
        elif isinstance(ty, TypeVar):
            return ty
        elif isinstance(ty, AbstractionType):
            return AbstractionType(
                ty.var_name,
                go(ctx, ty.var_type, not polarity),
                go(ctx, ty.type, polarity),
            )
        elif isinstance(ty, RefinedType):
            nt = go(ctx, ty.type, polarity)
            assert isinstance(nt, BaseType) or isinstance(nt, TypeVar)
            return RefinedType(ty.name, nt, ty.refinement)
        elif isinstance(ty, TypePolymorphism):
            return TypePolymorphism(
                ty.name,
                ty.kind,
                go(ctx, ty.body, polarity),
            )
        elif isinstance(ty, UnificationVar):
            if polarity:
                return Union(list(extract_direction(ty, True)))
            else:
                return Intersection(list(extract_direction(ty, False)))
        else:
            assert False

    return (go(ctx, ty, True), unions, intersections)


def remove_from_union_and_intersection(
    unions: list[Union],
    intersections: list[Intersection],
    to_be_removed: list[str],
):
    """Removes all unification vars whose name is in the to_be_removed list."""

    def rem(x: Type) -> bool:
        if isinstance(x, UnificationVar):
            return x.name not in to_be_removed
        else:
            return True

    for i in intersections:
        i.intersected = list(filter(rem, i.intersected))

    for union in unions:
        union.united = list(filter(rem, union.united))


def elaborate_remove_unification(ctx: TypingContext, t: Term) -> Term:
    if isinstance(t, Literal):
        return t
    elif isinstance(t, Var):
        return t
    elif isinstance(t, Hole):
        return t
    elif isinstance(t, Annotation):
        return Annotation(elaborate_remove_unification(ctx, t.expr), t.type)
    elif isinstance(t, TypeApplication):
        # Source: https://dl.acm.org/doi/pdf/10.1145/3409006
        nt, unions, intersections = replace_unification_variables(ctx, t.type)

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
                b
                for i in intersections
                if u in i.intersected
                for b in i.intersected
                if not isinstance(b, UnificationVar)
            ]
            # TODO: I think we need subtyping here.

            if any(bp in base_types_together_with_u_neg for bp in base_types_together_with_u_pos):
                to_be_removed.append(u.name)

        remove_from_union_and_intersection(
            unions,
            intersections,
            to_be_removed,
        )

        nt = remove_unions_and_intersections(ctx, nt)
        if isinstance(nt, Top):
            return TypeApplication(t.body, nt)
        else:
            should_be_refined = True
            if isinstance(t.body, Var):
                tat = ctx.type_of(t.body.name)
                if tat is not None and isinstance(tat, TypePolymorphism) and tat.kind == BaseKind():
                    should_be_refined = False

            if isinstance(nt, BaseType) or isinstance(nt, TypeVar):
                new_type: Type
                if should_be_refined:
                    new_var = ctx.fresh_var()
                    ref = LiquidHornApplication("k", [(LiquidVar(new_var), str(nt))])
                    new_type = RefinedType(new_var, nt, ref)
                else:
                    new_type = nt
                return TypeApplication(t.body, new_type)

            elif isinstance(nt, RefinedType):
                ref = LiquidHornApplication("k", [(LiquidVar(nt.name), str(nt.type))])
                new_type = RefinedType(nt.name, nt.type, ref)
                return TypeApplication(t.body, new_type)
            else:
                assert False

    elif isinstance(t, Abstraction):
        return Abstraction(
            t.var_name,
            elaborate_remove_unification(ctx, t.body),
        )
    elif isinstance(t, Let):
        nctx = ctx.with_var(t.var_name, bottom)  # bottom??
        return Let(
            t.var_name,
            elaborate_remove_unification(ctx, t.var_value),
            elaborate_remove_unification(nctx, t.body),
        )
    elif isinstance(t, Rec):
        nctx = ctx.with_var(t.var_name, t.var_type)
        return Rec(
            t.var_name,
            t.var_type,
            elaborate_remove_unification(nctx, t.var_value),
            elaborate_remove_unification(nctx, t.body),
        )
    elif isinstance(t, If):
        return If(
            elaborate_remove_unification(ctx, t.cond),
            elaborate_remove_unification(ctx, t.then),
            elaborate_remove_unification(ctx, t.otherwise),
        )
    elif isinstance(t, TypeAbstraction):
        return TypeAbstraction(
            t.name,
            t.kind,
            elaborate_remove_unification(
                ctx.with_typevar(t.name, t.kind),
                t.body,
            ),
        )
    elif isinstance(t, Application):
        return Application(
            elaborate_remove_unification(ctx, t.fun),
            elaborate_remove_unification(ctx, t.arg),
        )
    else:
        assert False


def elaborate(ctx: TypingContext, e: Term, expected_type: Type = top) -> Term:
    e2 = elaborate_foralls(e)
    e3 = elaborate_check(ctx, e2, expected_type)
    e4 = elaborate_remove_unification(ctx, e3)
    return e4
