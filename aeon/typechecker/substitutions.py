from ..types import Type, BasicType, RefinedType, AbstractionType, TypeApplication, TypeAbstraction, TypeException
from ..ast import Node, Application, Abstraction, TApplication, TAbstraction, Literal, Var, If, Hole


def substitution_expr_in_expr(n, replacement: Node, replaced):
    """ e[e/t] """

    if not issubclass(replacement.__class__, Node) or n == None:
        print("ooops1", type(replacement), replacement)

    r = lambda x: substitution_expr_in_expr(x, replacement, replaced)
    print("replacing type", n, n.type)
    nty = n.type == None and None or substitution_expr_in_type(
        n.type, replacement, replaced)
    if isinstance(n, Literal):
        return n
    elif isinstance(n, Var):
        if n.name == replaced:
            return replacement.with_type(nty)
        else:
            return n
    elif isinstance(n, If):
        return If(r(n.cond), r(n.then), r(n.otherwise)).with_type(nty)
    elif isinstance(n, Application):
        return Application(r(n.target), r(n.argument)).with_type(nty)
    elif isinstance(n, Abstraction):
        return Abstraction(n.arg_name, n.arg_type, r(n.body)).with_type(nty)
    elif isinstance(n, TApplication):
        arg = substitution_expr_in_type(n.argument, replacement, replaced)
        return TApplication(r(n.target), arg).with_type(nty)
    elif isinstance(n, TAbstraction):
        return TAbstraction(n.typevar, n.kind, r(n.body)).with_type(nty)
    elif isinstance(n, Hole):
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
    if isinstance(n, Literal):
        return n
    elif isinstance(n, Var):
        return n
    elif isinstance(n, If):
        return If(r(n.cond), r(n.then), r(n.otherwise)).with_type(nty)
    elif isinstance(n, Application):
        return Application(r(n.target), r(n.argument)).with_type(nty)
    elif isinstance(n, Abstraction):
        return Abstraction(n.arg_name, n.arg_type, r(n.body)).with_type(nty)
    elif isinstance(n, TApplication):
        targ = substitution_type_in_type(n.argument, replacement, replaced)
        return TApplication(r(n.target), targ).with_type(nty)
    elif isinstance(n, TAbstraction):
        return TAbstraction(n.typevar, n.kind, r(n.body)).with_type(nty)
    elif isinstance(n, Hole):
        return n
    else:
        raise Exception('No substitution rule for {}'.format(n))


def substitution_expr_in_type(n: Type, replacement: Node, replaced) -> Node:
    """ T[e/t] """
    #print(""" T[e/t] """, n, replacement, replaced)

    if not issubclass(replacement.__class__, Node):
        print("ooops3", type(replacement))

    if n == None:
        print("None in", n)
    r = lambda x: substitution_expr_in_type(x, replacement, replaced)
    re = lambda x: substitution_expr_in_expr(x, replacement, replaced)
    if isinstance(n, BasicType):
        return n
    elif isinstance(n, RefinedType):
        if re(n.cond) == None:
            print("FAIL HERE; BIG FAIL HERE")
        return RefinedType(n.name, r(n.type), re(n.cond))
    elif isinstance(n, AbstractionType):
        # TODO: verificar se é possível trocar o arg_name
        return AbstractionType(arg_name=n.arg_name,
                               arg_type=r(n.arg_type),
                               return_type=r(n.return_type))
    elif isinstance(n, TypeApplication):
        print("FOUND IN ", n)
        if r(n.target) == None:
            print("FAIL HERE; BIG FAIL HERE 131")
        return TypeApplication(target=r(n.target), argument=r(n.argument))
    elif isinstance(n, TypeAbstraction):
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(n.type))
    else:
        raise TypeException("Substitution in type unknown:", n, type(n))


def substitution_type_in_type(n, replacement: Type, replaced: str):
    """ T[U/V] """
    #print(""" T[U/V] """, n, replacement, replaced)

    if not issubclass(replacement.__class__, Type):
        print("ooops4", type(replacement))

    if n == None:
        return n
    r = lambda x: substitution_type_in_type(x, replacement, replaced)
    if isinstance(n, BasicType):
        if n.name == replaced:
            return replacement
        else:
            return n
    elif isinstance(n, RefinedType):
        new_cond = substitution_type_in_expr(n.cond, replacement, replaced)
        return RefinedType(n.name, r(n.type), new_cond)
    elif isinstance(n, AbstractionType):
        return AbstractionType(arg_name=n.arg_name,
                               arg_type=r(n.arg_type),
                               return_type=r(n.return_type))
    elif isinstance(n, TypeApplication):
        return TypeApplication(target=r(n.target), argument=r(n.argument))
    elif isinstance(n, TypeAbstraction):
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(n.type))
    else:
        raise TypeException("Substitution type/type unknown:", n, type(n))
