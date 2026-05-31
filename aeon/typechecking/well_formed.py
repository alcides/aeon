from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import AbstractionType, RefinementPolymorphism, Top, TypeConstructor
from aeon.core.types import ExistentialType
from aeon.core.types import Kind
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import TypingContext
from aeon.typechecking.liquid import typecheck_liquid
from aeon.utils.name import Name


def wf_inner(ctx: TypingContext, t: Type, k: Kind = Kind.STAR) -> bool:
    match t:
        case Top():
            return True  # wf_no_refinement
        case RefinedType(name, TypeConstructor(_, _) as ty, refinement):
            inferred_type = typecheck_liquid(ctx.with_var(name, ty), refinement)
            return inferred_type == t_bool
        case TypeVar(tvname):
            return tvname in [v[0] for v in ctx.typevars()]
        case RefinedType(name, TypeVar(tvname), LiquidLiteralBool(True)):
            return (tvname, k) in ctx.typevars()
        case RefinedType(name, TypeVar(tvname) as ty, refinement):
            return (
                k == Kind.BASE
                and (tvname, Kind.BASE) in ctx.typevars()
                and typecheck_liquid(ctx.with_var(name, ty), refinement) == t_bool
            )
        case AbstractionType(aname, atype, rtype):
            return k == Kind.STAR and wellformed(ctx, atype) and wellformed(ctx.with_var(aname, atype), rtype)
        case TypePolymorphism(name, kind, body):
            return k == Kind.STAR and wellformed(ctx.with_typevar(name, kind), body)
        case RefinementPolymorphism(name, sort, body):
            pred_type = AbstractionType(Name("_", 0), sort, t_bool)
            return k == Kind.STAR and wellformed(ctx, sort) and wellformed(ctx.with_var(name, pred_type), body)
        case TypeConstructor(name, args):
            if not args:
                return ctx.get_type_constructor(name) is not None
            else:
                cargs = ctx.get_type_constructor(name)
                if not cargs or len(cargs) != len(args):
                    return False
                # Type-constructor arguments are base types (with optional
                # refinement); use ``wellformed`` so refined type variables
                # like ``{_r:a | p _r}`` (which need Kind.BASE) are accepted
                # in positions like ``List a<p>`` or ``Pair a<p> b<q>``.
                return all(wellformed(ctx, t) for t in args)
        case RefinedType(name, TypeConstructor(_, args) as ity, refinement):
            return wf_inner(ctx, ity) and typecheck_liquid(ctx.with_var(name, ity), refinement) == t_bool
        case ExistentialType(binders, body):
            ext_ctx = ctx
            for bn, bt in binders:
                if not wellformed(ext_ctx, bt):
                    return False
                ext_ctx = ext_ctx.with_var(bn, bt)
            return wellformed(ext_ctx, body, k)
        case _:
            return False


def wellformed(ctx: TypingContext, t: Type, k: Kind = Kind.STAR) -> bool:
    match k:
        case Kind.STAR:
            return wf_inner(ctx, t, Kind.STAR) or wf_inner(ctx, t, Kind.BASE)
        case _:
            return wf_inner(ctx, t, Kind.BASE)
