from typing import Optional

from ..types import Type, BasicType, RefinedType, AbstractionType, TypeApplication, TypeAbstraction, TypeException
from ..ast import TypedNode, Application, Abstraction, TApplication, TAbstraction, Literal, Var, If, Hole

from .exceptions import TypingException


class SubstitutionException(TypingException):
    pass


def substitution_expr_in_expr(n, replacement: TypedNode,
                              replaced: str) -> TypedNode:
    """ e[e/t] """
    assert (isinstance(replacement, TypedNode))
    assert (n != None)
    assert (isinstance(replaced, str))

    r = lambda x: substitution_expr_in_expr(x, replacement, replaced)
    nty = n.type and substitution_expr_in_type(n.type, replacement, replaced)
    if isinstance(n, Literal):
        return n
    elif isinstance(n, Var):
        if n.name == replaced:
            return replacement.with_type(nty)
        else:
            return n.with_type(nty)
    elif isinstance(n, If):
        return If(r(n.cond), r(n.then), r(n.otherwise)).with_type(nty)
    elif isinstance(n, Application):
        return Application(r(n.target), r(n.argument)).with_type(nty)
    elif isinstance(n, Abstraction):
        if n.arg_name == replaced:
            return n
        return Abstraction(n.arg_name, n.arg_type, r(n.body)).with_type(nty)
    elif isinstance(n, TApplication):
        arg = substitution_expr_in_type(n.argument, replacement, replaced)
        return TApplication(r(n.target), arg).with_type(nty)
    elif isinstance(n, TAbstraction):
        if n.typevar == replaced:
            return n
        return TAbstraction(n.typevar, n.kind, r(n.body)).with_type(nty)
    elif isinstance(n, Hole):
        return n.with_type(nty)
    else:
        raise SubstitutionException('No substitution rule for {}'.format(n))


def substitution_type_in_expr(n: TypedNode, replacement: Type,
                              replaced: str) -> TypedNode:
    """ e[e/T] """

    assert (isinstance(n, TypedNode))
    assert (n != None)
    assert (isinstance(replaced, str))

    r = lambda x: substitution_type_in_expr(x, replacement, replaced)
    nty = n.type
    if nty:
        nty = substitution_type_in_type(n.type, replacement, replaced)
    if isinstance(n, Literal):
        return n.with_type(nty)
    elif isinstance(n, Var):
        return n.with_type(nty)
    elif isinstance(n, If):
        return If(r(n.cond), r(n.then), r(n.otherwise)).with_type(nty)
    elif isinstance(n, Application):
        return Application(r(n.target), r(n.argument)).with_type(nty)
    elif isinstance(n, Abstraction):
        if n.arg_name == replaced:
            return n
        return Abstraction(n.arg_name, n.arg_type, r(n.body)).with_type(nty)
    elif isinstance(n, TApplication):
        targ = substitution_type_in_type(n.argument, replacement, replaced)
        return TApplication(r(n.target), targ).with_type(nty)
    elif isinstance(n, TAbstraction):
        if n.typevar == replaced:
            return n
        return TAbstraction(n.typevar, n.kind, r(n.body)).with_type(nty)
    elif isinstance(n, Hole):
        return n.with_type(nty)
    else:
        raise Exception('No substitution rule for {}'.format(n))


def substitution_expr_in_type(n: Type, replacement: TypedNode,
                              replaced: str) -> Type:
    """ T[e/t] """

    assert (isinstance(n, Type))
    assert (isinstance(replaced, str))

    r = lambda x: substitution_expr_in_type(x, replacement, replaced)
    re = lambda x: substitution_expr_in_expr(x, replacement, replaced)
    if isinstance(n, BasicType):
        return n
    elif isinstance(n, RefinedType):
        if n.name == replaced:
            return n
        return RefinedType(n.name, r(n.type), re(n.cond))
    elif isinstance(n, AbstractionType):
        if n.arg_name == replaced:
            return n
        return AbstractionType(arg_name=n.arg_name,
                               arg_type=r(n.arg_type),
                               return_type=r(n.return_type))
    elif isinstance(n, TypeApplication):
        return TypeApplication(target=r(n.target), argument=r(n.argument))
    elif isinstance(n, TypeAbstraction):
        if n.name == replaced:
            return n
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(n.type))
    else:
        raise TypeException("Substitution in type unknown:", n, type(n))


def substitution_type_in_type(n: Type, replacement: Type,
                              replaced: str) -> Type:
    """ T[U/V] """
    assert (isinstance(n, Type))
    assert (isinstance(replaced, str))

    r = lambda x: substitution_type_in_type(x, replacement, replaced)
    re = lambda x: substitution_type_in_expr(x, replacement, replaced)

    if isinstance(n, BasicType):
        if n.name == replaced:
            return replacement
        else:
            return n
    elif isinstance(n, RefinedType):
        if n.name == replaced:
            return n
        new_cond = substitution_type_in_expr(n.cond, replacement, replaced)
        return RefinedType(n.name, r(n.type), new_cond)
    elif isinstance(n, AbstractionType):
        if n.arg_name == replaced:
            return n
        return AbstractionType(arg_name=n.arg_name,
                               arg_type=r(n.arg_type),
                               return_type=r(n.return_type))
    elif isinstance(n, TypeApplication):
        return TypeApplication(target=r(n.target), argument=r(n.argument))
    elif isinstance(n, TypeAbstraction):
        if n.name == replaced:
            return n
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(n.type))
    else:
        raise TypeException("Substitution type/type unknown:", n, type(n))
