from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import AbstractionType, BaseKind, Top, TypeConstructor
from aeon.core.types import BaseType
from aeon.core.types import Kind
from aeon.core.types import RefinedType
from aeon.core.types import StarKind
from aeon.core.types import t_bool
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import TypingContext
from aeon.typechecking.liquid import typecheck_liquid


def wf_inner(ctx: TypingContext, t: Type, k: Kind = StarKind()) -> bool:
    match t:
        case Top():
            return True  # wf_no_refinement
        case BaseType(name):
            return ctx.get_type_constructor(name) is not None
        case RefinedType(name, BaseType(_) as ty, refinement):
            inferred_type = typecheck_liquid(ctx.with_var(name, ty),
                                             refinement)
            return inferred_type == t_bool
        case TypeVar(tvname):
            return tvname in [v[0] for v in ctx.typevars()]
        case RefinedType(name, TypeVar(tvname), LiquidLiteralBool(True)):
            return (tvname, k) in ctx.typevars()
        case RefinedType(name, TypeVar(tvname) as ty, refinement):
            return (k == BaseKind() and (tvname, BaseKind()) in ctx.typevars()
                    and typecheck_liquid(ctx.with_var(name, ty),
                                         refinement) == t_bool)
        case AbstractionType(aname, atype, rtype):
            return k == StarKind() and wellformed(ctx, atype) and wellformed(
                ctx.with_var(aname, atype), rtype)
        case TypePolymorphism(name, kind, body):
            return k == StarKind() and wellformed(ctx.with_typevar(name, kind),
                                                  body)
        case TypeConstructor(name, args):
            cargs = ctx.get_type_constructor(name)
            if not cargs or len(cargs) != len(args):
                return False
            return all(wf_inner(ctx, t) for t in args)
        case RefinedType(name, TypeConstructor(_, args) as ity, refinement):
            return wf_inner(ctx, ity) and typecheck_liquid(
                ctx.with_var(name, ity), refinement) == t_bool
        case _:
            return False


def wellformed(ctx: TypingContext, t: Type, k: Kind = StarKind()) -> bool:
    match k:
        case StarKind():
            return wf_inner(ctx, t, StarKind()) or wf_inner(ctx, t, BaseKind())
        case _:
            return wf_inner(ctx, t, BaseKind())
