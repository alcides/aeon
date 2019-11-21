from typing import Optional

from ..types import Type, BasicType, RefinedType, AbstractionType, TypeApplication, TypeAbstraction, TypeException
from ..ast import TypedNode, Application, Abstraction, TApplication, TAbstraction, Literal, Var, If, Hole

from .exceptions import TypingException


class SubstitutionException(TypingException):
    pass


def substitution_expr_in_expr(n, replacement: TypedNode,
                              replaced: str) -> TypedNode:
    """ e[e/x] """
    assert (isinstance(replacement, TypedNode))
    assert (n != None)
    assert (isinstance(replaced, str))

    r = lambda x: substitution_expr_in_expr(x, replacement, replaced)
    nty = n.type if n.type == None else substitution_expr_in_type(
        n.type, replacement, replaced)
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
        new_name = n.arg_name
        new_body = n.body
        if isinstance(replacement, Var) and new_name == replacement.name:
            new_name = new_name + "_fresh"
            new_body = substitution_expr_in_expr(new_body, Var(new_name),
                                                 n.arg_name)
        return Abstraction(new_name, n.arg_type, r(new_body)).with_type(nty)
    elif isinstance(n, TApplication):
        arg = substitution_expr_in_type(n.argument, replacement, replaced)
        return TApplication(r(n.target), arg).with_type(nty)
    elif isinstance(n, TAbstraction):
        if n.typevar == replaced:
            return n
        new_name = n.typevar
        new_body = n.body
        if isinstance(replacement, Var) and new_name == replacement.name:
            new_name = new_name + "_fresh"
            new_body = substitution_expr_in_expr(new_body, Var(new_name),
                                                 n.typevar)
        return TAbstraction(n.typevar, n.kind, r(n.body)).with_type(nty)
    elif isinstance(n, Hole):
        return n.with_type(nty)
    else:
        raise SubstitutionException('No substitution rule for {}'.format(n))


def substitution_type_in_expr(n: TypedNode, replacement: Type,
                              replaced: str) -> TypedNode:
    """ e[T/t] """

    assert (isinstance(n, TypedNode))
    assert (n != None)
    assert (isinstance(replaced, str))

    r = lambda x: substitution_type_in_expr(x, replacement, replaced)
    nty = n.type if n.type == None else substitution_type_in_type(
        n.type, replacement, replaced)
    if isinstance(n, Literal):
        return n
    elif isinstance(n, Var):
        return n.with_type(nty)
    elif isinstance(n, If):
        return If(r(n.cond), r(n.then), r(n.otherwise)).with_type(nty)
    elif isinstance(n, Application):
        return Application(r(n.target), r(n.argument)).with_type(nty)
    elif isinstance(n, Abstraction):
        if n.arg_name == replaced:
            return n
        new_name = n.arg_name
        new_body = n.body
        if isinstance(replacement, BasicType) and new_name == replacement.name:
            new_name = new_name + "_fresh"
            new_body = substitution_expr_in_expr(new_body, Var(new_name),
                                                 n.arg_name)
        return Abstraction(new_name, n.arg_type, r(new_body)).with_type(nty)
    elif isinstance(n, TApplication):
        targ = substitution_type_in_type(n.argument, replacement, replaced)
        return TApplication(r(n.target), targ).with_type(nty)
    elif isinstance(n, TAbstraction):
        if n.typevar == replaced:
            return n
        new_name = n.typevar
        new_body = n.body
        if isinstance(replacement, BasicType) and new_name == replacement.name:
            new_name = new_name + "_fresh"
            new_body = substitution_type_in_expr(new_body, BasicType(new_name),
                                                 n.typevar)
        return TAbstraction(new_name, n.kind, r(new_body)).with_type(nty)
    elif isinstance(n, Hole):
        return n.with_type(nty)
    else:
        raise Exception('No substitution rule for {}'.format(n))


def substitution_expr_in_type(n: Type, replacement: TypedNode,
                              replaced: str) -> Type:
    """ T[e/x] """

    assert (isinstance(n, Type))
    assert (isinstance(replaced, str))

    r = lambda x: substitution_expr_in_type(x, replacement, replaced)
    re = lambda x: substitution_expr_in_expr(x, replacement, replaced)
    if isinstance(n, BasicType):
        return n
    elif isinstance(n, RefinedType):
        if n.name == replaced:
            return n
        new_name = n.name
        new_cond = n.cond
        if isinstance(replacement, Var) and new_name == replacement.name:
            new_name = new_name + "_fresh"
            new_cond = substitution_expr_in_expr(new_cond, Var(new_name),
                                                 n.name)
        return RefinedType(new_name, r(n.type), re(new_cond))
    elif isinstance(n, AbstractionType):
        if n.arg_name == replaced:
            return n
        new_name = n.arg_name
        new_body = n.return_type
        if isinstance(replacement, Var) and new_name == replacement.name:
            new_name = new_name + "_fresh"
            new_body = substitution_expr_in_type(new_body, Var(new_name),
                                                 n.arg_name)
        return AbstractionType(arg_name=new_name,
                               arg_type=r(n.arg_type),
                               return_type=r(new_body))
    elif isinstance(n, TypeApplication):
        return TypeApplication(target=r(n.target), argument=r(n.argument))
    elif isinstance(n, TypeAbstraction):
        if n.name == replaced:
            return n
        new_name = n.name
        new_type = n.type
        if isinstance(replacement, Var) and new_name == replacement.name:
            new_name = new_name + "_fresh"
            new_type = substitution_type_in_type(new_type, BasicType(new_name),
                                                 n.name)
        return TypeAbstraction(name=new_name, kind=n.kind, type=r(new_type))
    else:
        raise TypeException("Substitution in type unknown:", n, type(n))


def substitution_type_in_type(n: Type, replacement: Type,
                              replaced: str) -> Type:
    """ T[U/t] """
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
        new_name = n.name
        new_cond = n.cond
        if isinstance(replacement, BasicType) and new_name == replacement.name:
            new_name = new_name + "_fresh"
            new_cond = substitution_expr_in_expr(new_cond, Var(new_name),
                                                 n.name)
        new_cond = substitution_type_in_expr(new_cond, replacement, replaced)
        return RefinedType(n.name, r(n.type), new_cond)
    elif isinstance(n, AbstractionType):
        new_name = n.arg_name
        new_body = n.return_type
        if isinstance(replacement, BasicType) and new_name == replacement.name:
            new_name = new_name + "_fresh"
            new_body = substitution_expr_in_type(new_body, Var(new_name),
                                                 n.arg_name)
        return AbstractionType(arg_name=new_name,
                               arg_type=r(n.arg_type),
                               return_type=r(new_body))
    elif isinstance(n, TypeApplication):
        return TypeApplication(target=r(n.target), argument=r(n.argument))
    elif isinstance(n, TypeAbstraction):
        new_name = n.name
        new_type = n.type
        if isinstance(replacement, BasicType) and new_name == replacement.name:
            new_name = new_name + "_fresh"
            new_type = substitution_type_in_type(new_type, BasicType(new_name),
                                                 n.name)
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(new_type))
    else:
        raise TypeException("Substitution type/type unknown:", n, type(n))


def rename_abs(e: Abstraction, new: str):
    nret = substitution_expr_in_expr(e.body, Var(new), e.arg_name)
    return Abstraction(new, e.arg_type, nret)


def rename_tabs(e: TAbstraction, new: str):
    nret = substitution_type_in_expr(e.body, BasicType(new), e.typevar)
    return TAbstraction(new, e.kind, nret)
