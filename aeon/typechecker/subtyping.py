from ..types import TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b, t_delegate
from ..ast import Var, TAbstraction, TApplication, Application, Abstraction, Literal

from .substitutions import substitution_expr_in_type, substitution_type_in_type, \
    substitution_expr_in_expr, substitution_type_in_expr
from .zed import is_satisfiable, entails
from .typechecker import check_type

from .exceptions import TypingException


class SubtypingException(TypingException):
    pass


def sub_base(ctx, sub: BasicType, sup: BasicType):
    """ S-Int, S-Bool, S-Var """
    return sub.name == sup.name


def sub_whereL(ctx, sub: RefinedType, sup: Type):
    """ S-WhereL """
    nctx = ctx.with_var(sub.name, sub.type)
    return check_type(nctx, sub.cond, t_b) and \
        is_satisfiable(nctx, sub.cond) and \
        is_subtype(ctx, sub.type, sup)


def sub_whereR(ctx, sub: Type, sup: RefinedType):
    """ S-WhereR """
    nctx = ctx.with_var(sup.name, sub)
    return is_subtype(ctx, sub, sup.type) and \
        entails(nctx, sup.cond)


def sub_abs(ctx, sub: AbstractionType, sup: AbstractionType):
    """ S-Abs """
    nctx = ctx.with_var(sup.arg_name, sup.arg_type)
    sub_return_type = substitution_expr_in_type(sub.return_type,
                                                Var(sup.arg_name),
                                                sub.arg_name)
    return is_subtype(ctx, sup.arg_type, sub.arg_type) and \
        is_subtype(nctx, sub_return_type, sup.return_type)


def sub_tabs(ctx, sub: TypeAbstraction, sup: TypeAbstraction):
    """ S-TAbs """
    nctx = ctx.with_type_var(sup.name, sup.kind)
    return is_subtype(
        nctx, substitution_type_in_type(sub.type, BasicType(sup.name),
                                        sub.name), sup.type)


def sub_tappL(ctx, sub: TypeApplication, sup: Type):
    """ S-Cong + C-Beta on the left """
    #c_beta
    abst: TypeAbstraction = sub.target
    assert (type(sub.target) == TypeAbstraction)
    nsub = substitution_type_in_type(abst.type, sub.argument, abst.name)
    return is_subtype(ctx, nsub, sup)


def sub_tappR(ctx, sub: Type, sup: TypeApplication):
    """ S-Cong . C-Beta on the right"""
    abst = sup.target
    assert (type(sub.target) == TypeAbstraction)
    nsup = substitution_type_in_type(abst.type, sup.argument, abst.name)
    return is_subtype(ctx, sub, nsup)


def is_subtype(ctx, sub, sup) -> bool:
    """ Subtyping Rules """
    if isinstance(sub, BasicType) and sub.name == 'Bottom':
        return True
    elif isinstance(sup, BasicType) and sup.name == 'Top':
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

    raise SubtypingException('No subtyping rule for {} <: {}'.format(sub, sup))
