from .types import *
from .ast import *


def substitution_expr_in_expr(n, replacement: Node, replaced):
    """ e[e/t] """

    if not issubclass(replacement.__class__, Node):
        print("ooops1", type(replacement), replacement)

    #print(""" e[e/t] """, n, replacement, replaced)
    r = lambda x: substitution_expr_in_expr(x, replacement, replaced)
    nty = n.type == None and None or substitution_expr_in_type(
        n.type, replacement, replaced)
    if type(n) is Literal:
        return n
    elif type(n) is Var:
        if n.name == replaced:
            return replacement.with_type(nty)
        else:
            return n
    elif type(n) is If:
        return If(r(n.cond), r(n.then), r(n.otherwise)).with_type(nty)
    elif type(n) is Application:
        return Application(r(n.target), r(n.argument)).with_type(nty)
    elif type(n) is Abstraction:
        return Abstraction(n.arg_name, n.arg_type, r(n.body)).with_type(nty)
    elif type(n) is TApplication:
        arg = substitution_expr_in_type(n.argument, replacement, replaced)
        return TApplication(r(n.target), arg).with_type(nty)
    elif type(n) is TAbstraction:
        return TAbstraction(n.typevar, n.kind, r(n.body)).with_type(nty)
    elif type(n) is Hole:
        return n
    else:
        raise Exception('No substitution rule for {}'.format(n))


def substitution_type_in_expr(n: Node, replacement: Type, replaced):
    """ e[e/T] """

    if not issubclass(replacement.__class__, Type):
        print("ooops2", type(replacement))

    #print(""" e[e/T] """, n, replacement, replaced)
    r = lambda x: substitution_type_in_expr(x, replacement, replaced)
    nty = n.type == None and None or substitution_type_in_type(
        n.type, replacement, replaced)
    if type(n) is Literal:
        return n
    elif type(n) is Var:
        return n
    elif type(n) is If:
        return If(r(n.cond), r(n.then), r(n.otherwise)).with_type(nty)
    elif type(n) is Application:
        return Application(r(n.target), r(n.argument)).with_type(nty)
    elif type(n) is Abstraction:
        return Abstraction(n.arg_name, n.arg_type, r(n.body)).with_type(nty)
    elif type(n) is TApplication:
        targ = substitution_type_in_type(n.argument, replacement, replaced)
        return TApplication(r(n.target), targ).with_type(nty)
    elif type(n) is TAbstraction:
        return TAbstraction(n.typevar, n.kind, r(n.body)).with_type(nty)
    elif type(n) is Hole:
        return n
    else:
        raise Exception('No substitution rule for {}'.format(n))


def substitution_expr_in_type(n: Type, replacement: Node, replaced):
    """ T[e/t] """
    #print(""" T[e/t] """, n, replacement, replaced)

    if not issubclass(replacement.__class__, Node):
        print("ooops3", type(replacement))

    if n == None:
        return n
    r = lambda x: substitution_expr_in_type(x, replacement, replaced)
    re = lambda x: substitution_expr_in_expr(x, replacement, replaced)
    if type(n) is BasicType:
        return n
    elif type(n) is RefinedType:
        return RefinedType(n.name, r(n.type), re(n.cond))
    elif type(n) is AbstractionType:
        # TODO: verificar se é possível trocar o arg_name
        return AbstractionType(name=n.name,
                               arg_type=r(n.arg_type),
                               return_type=r(n.return_type))
    elif type(n) is TypeApplication:
        return TypeApplication(target=re(n.target), argument=r(n.argument))
    elif type(n) is TypeAbstraction:
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(n.type))
    else:
        raise TypeException("Substitution in type unknown:", n, type(n))


def substitution_type_in_type(n, replacement: Type, replaced):
    """ T[U/V] """
    #print(""" T[U/V] """, n, replacement, replaced)

    if not issubclass(replacement.__class__, Type):
        print("ooops4", type(replacement))

    if n == None:
        return n
    r = lambda x: substitution_type_in_type(x, replacement, replaced)
    if type(n) is BasicType:
        if n.typeName == replaced:
            return replacement
        else:
            return n
    elif type(n) is RefinedType:
        new_cond = substitution_type_in_expr(n.cond, replacement, replaced)
        return RefinedType(n.name, r(n.type), new_cond)
    elif type(n) is AbstractionType:
        return AbstractionType(name=n.name,
                               arg_type=r(n.arg_type),
                               return_type=r(n.return_type))
    elif type(n) is TypeApplication:
        return TypeApplication(target=r(n.target), argument=r(n.argument))
    elif type(n) is TypeAbstraction:
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(n.type))
    else:
        raise TypeException("Substitution type/type unknown:", n, type(n))
