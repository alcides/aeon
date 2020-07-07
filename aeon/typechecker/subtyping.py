from ..types import TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b, t_delegate
from ..ast import Var, TAbstraction, TApplication, Application, Abstraction, Literal

from .conversions import type_conversion
from .substitutions import substitution_expr_in_type, substitution_type_in_type, \
    substitution_expr_in_expr, substitution_type_in_expr
from .zed import is_satisfiable, entails
from .kinding import check_kind
from .exceptions import TypingException


class SubtypingException(TypingException):
    pass


def sub_base(ctx, sub: BasicType, sup: BasicType) -> bool:
    """ S-Int, S-Bool, S-Var """
    return sub.name == sup.name


def sub_whereL(ctx, sub: RefinedType, sup: Type) -> bool:
    """ S-WhereL """
    from .typing import check_type
    nctx = ctx.with_var(sub.name, sub.type)
    check_type(nctx.with_uninterpreted(), sub.cond, t_b)

    return check_type(nctx.with_uninterpreted(), sub.cond, t_b) and \
        is_subtype(ctx, sub.type, sup)


def sub_whereR(ctx, sub: Type, sup: RefinedType) -> bool:
    """ S-WhereR """
    nctx = ctx.with_var(sup.name, sub)

    return is_subtype(nctx.with_uninterpreted(), sub, sup.type) and \
        entails(nctx.with_uninterpreted(), sup.cond)


def sub_abs(ctx, sub: AbstractionType, sup: AbstractionType) -> bool:
    """ S-Abs """
    nctx = ctx.with_var(sup.arg_name, sup.arg_type)
    sub_return_type = substitution_expr_in_type(sub.return_type,
                                                Var(sup.arg_name),
                                                sub.arg_name)
    check_kind(ctx, sub.arg_type, star)
    check_kind(nctx, sup.return_type, star)
    return is_subtype(ctx, sup.arg_type, sub.arg_type) and \
        is_subtype(nctx, sub_return_type, sup.return_type)


def sub_tabs(ctx, sub: TypeAbstraction, sup: TypeAbstraction) -> bool:
    """ S-TAbs """
    nctx = ctx.with_type_var(sup.name, sup.kind)
    return is_subtype(
        nctx, substitution_type_in_type(sub.type, BasicType(sup.name),
                                        sub.name), sup.type)


def sub_tapp(ctx, sub: TypeApplication, sup: TypeApplication) -> bool:
    if not is_subtype(ctx, sub.target, sup.target):
        raise SubtypingException(
            "Type constructor is not the same: {} and {} in {} <?: {}".format(
                sub.target, sup.target, sub, sup))
    # TODO: Substitute kind
    return is_subtype(ctx, sub.argument, sup.argument)


def sub_tappL(ctx, sub: TypeApplication, sup: Type) -> bool:
    """ S-TappL """
    abst = type_conversion(sub.target)
    if not isinstance(abst, TypeAbstraction):
        raise SubtypingException("{} is not a TypeAbstraction in {}.".format(
            abst, sub))
    check_kind(ctx, sub.argument, abst.kind)
    nsub = substitution_type_in_type(abst.type, sub.argument, abst.name)
    return is_subtype(ctx, nsub, sup)


def sub_tappR(ctx, sub: Type, sup: TypeApplication) -> bool:
    """ S-TappR """
    abst = type_conversion(sup.target)
    if not isinstance(abst, TypeAbstraction):
        raise SubtypingException("{} is not a TypeAbstraction in {}.".format(
            abst, sub))
    check_kind(ctx, sup.argument, abst.kind)
    nsup = substitution_type_in_type(abst.type, sup.argument, abst.name)
    return is_subtype(ctx, sub, nsup)


def is_subtype(ctx, sub, sup) -> bool:
    """ Subtyping Rules """
    
    # ===
    # Small hack because of type_aliases that are not replaced
    if isinstance(sub, BasicType) and sub.name in ctx.type_aliases:
        return is_subtype(ctx, ctx.type_aliases[sub.name], sup)
    if isinstance(sup, BasicType) and sup.name in ctx.type_aliases:
        return is_subtype(ctx, sub, ctx.type_aliases[sup.name])
    # ===

    if isinstance(sub, BasicType) and sub.name == 'Bottom':
        return True
    elif isinstance(sup, BasicType) and sup.name in ['Top', 'Object', 'Void']:
        return True
    elif isinstance(sub, BasicType) and isinstance(sup, BasicType):
        return sub_base(ctx, sub, sup)
    elif isinstance(sup, RefinedType):
        return sub_whereR(ctx, sub, sup)
    elif isinstance(sub, RefinedType):
        return sub_whereL(ctx, sub, sup)
    elif isinstance(sub, AbstractionType) and isinstance(sup, AbstractionType):
        return sub_abs(ctx, sub, sup)
    elif isinstance(sub, TypeAbstraction) and isinstance(sup, TypeAbstraction):
        return sub_tabs(ctx, sub, sup)
    elif isinstance(sub, TypeApplication) and isinstance(sup, TypeApplication):
        return sub_tapp(ctx, sub, sup)
    elif isinstance(sub, TypeApplication):
        return sub_tappL(ctx, sub, sup)
    elif isinstance(sup, TypeApplication):
        return sub_tappR(ctx, sub, sup)
    #raise SubtypingException('No subtyping rule for {} <: {}'.format(sub, sup))
    return False
