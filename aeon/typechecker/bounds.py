from ..types import Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, TypeApplication, \
    top, bottom
from ..ast import Var, Application
from .substitutions import substitution_expr_in_type, substitution_expr_in_expr
from .conversions import type_conversion


def lub(T: Type, U: Type) -> Type:
    """ T ⊔ U  """
    T = type_conversion(T)
    U = type_conversion(U)
    if isinstance(T, BasicType) and isinstance(U,
                                               BasicType) and T.name == U.name:
        return T
    elif isinstance(T, BasicType) and isinstance(U, RefinedType):
        return lub(T, U.type)
    elif isinstance(T, RefinedType) and isinstance(U, BasicType):
        return lub(T.type, U)
    elif isinstance(T, RefinedType) and isinstance(U, RefinedType):
        return lub_where(T, U)
    elif isinstance(T, AbstractionType) and isinstance(U, AbstractionType):
        return lub_abs(T, U)
    elif isinstance(T, TypeAbstraction) and isinstance(
            U, TypeAbstraction) and T.kind == U.kind:
        return lub_tabs(T, U)
    elif isinstance(T, TypeApplication) and isinstance(U, TypeApplication):
        return lub_tapp(T, U)
    return top


def lub_where(T: RefinedType, U: RefinedType) -> RefinedType:
    new_U_type = substitution_expr_in_type(U.type, Var(T.name), U.name)
    new_U_cond = substitution_expr_in_expr(U.cond, Var(T.name), U.name)
    ncond = Application(Application(Var("||"), T.cond), new_U_cond)
    return RefinedType(T.name, lub(T.type, new_U_type), ncond)


def lub_abs(T: AbstractionType, U: AbstractionType) -> AbstractionType:
    new_U = substitution_expr_in_type(U.return_type, Var(T.arg_name),
                                      U.arg_name)
    I = glb(T.arg_type, U.arg_type)
    O = lub(T.return_type, new_U)
    return AbstractionType(T.arg_name, I, O)


def lub_tabs(T: TypeAbstraction, U: TypeAbstraction) -> TypeAbstraction:
    new_U = substitution_expr_in_type(U.type, Var(T.name), U.name)
    N = lub(T.type, new_U)
    return TypeAbstraction(T.name, T.kind, N)


def lub_tapp(T: TypeApplication, U: TypeApplication) -> TypeApplication:
    F = lub(T.target, U.target)
    X = lub(T.argument, U.argument)
    return TypeApplication(F, X)


def glb(T: Type, U: Type) -> Type:
    """ T ⊓ U  """
    T = type_conversion(T)
    U = type_conversion(U)
    if isinstance(T, BasicType) and isinstance(U,
                                               BasicType) and T.name == U.name:
        return T
    elif isinstance(T, BasicType) and isinstance(U, RefinedType):
        return RefinedType(U.name, glb(T, U.type), U.cond)
    elif isinstance(T, RefinedType) and isinstance(U, BasicType):
        return RefinedType(T.name, glb(T.type, U), T.cond)
    elif isinstance(T, RefinedType) and isinstance(U, RefinedType):
        return glb_where(T, U)
    elif isinstance(T, AbstractionType) and isinstance(U, AbstractionType):
        return glb_abs(T, U)
    elif isinstance(T, TypeAbstraction) and isinstance(
            U, TypeAbstraction) and T.kind == U.kind:
        return glb_tabs(T, U)
    elif isinstance(T, TypeApplication) and isinstance(U, TypeApplication):
        return glb_tapp(T, U)

    return bottom


def glb_abs(T: AbstractionType, U: AbstractionType) -> AbstractionType:
    new_U = substitution_expr_in_type(U.return_type, Var(T.arg_name),
                                      U.arg_name)
    I = lub(T.arg_type, U.arg_type)
    O = glb(T.return_type, new_U)
    return AbstractionType(T.arg_name, I, O)


def glb_where(T: RefinedType, U: RefinedType) -> RefinedType:
    new_U_type = substitution_expr_in_type(U.type, Var(T.name), U.name)
    new_U_cond = substitution_expr_in_expr(U.cond, Var(T.name), U.name)
    ncond = Application(Application(Var("&&"), T.cond), new_U_cond)
    return RefinedType(T.name, glb(T.type, new_U_type), ncond)


def glb_tabs(T: TypeAbstraction, U: TypeAbstraction) -> TypeAbstraction:
    new_U = substitution_expr_in_type(U.type, Var(T.name), U.name)
    N = glb(T.type, new_U)
    return TypeAbstraction(T.name, T.kind, N)


def glb_tapp(T: TypeApplication, U: TypeApplication) -> TypeApplication:
    F = glb(T.target, U.target)
    X = glb(T.argument, U.argument)
    return TypeApplication(F, X)
