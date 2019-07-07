from .types import *
from .ast import *


def substitution_in_expr(n, replacement, replaced):
    """ e[t'/t] """
    r = lambda x: substitution_in_expr(x, replacement, replaced)

    nty = substitution_var_in_type(n.type, replacement, replaced)
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
    elif type(n) is TApplication:
        return TApplication(r(n.target), n.argument).with_type(nty)
    elif type(n) is TAbstraction:
        n = TAbstraction(t.arg_name, t.arg_type, r(t.body)).with_type(nty)
    else:
        raise Exception('No substitution rule for {}'.format(n))


def substitution_var_in_type(n: Type, replacement, replaced):
    """ T[t'/t] """
    r = lambda x: substitution_var_in_type(x, replacement, replaced)
    if type(n) is BasicType:
        return n
    elif type(n) is RefinedType:
        return RefinedType(n.name, r(n.type),
                           substitution_in_expr(n.cond, replacement, replaced))
    elif type(n) is ArrowType:
        # TODO: verificar se é possível trocar o arg_name
        return ArrowType(arg_name=n.arg_name,
                         arg_type=r(n.arg_type),
                         return_type=r(n.return_type))
    elif type(n) is TypeApplication:
        return TypeApplication(target=r(n.target), argument=r(n.argument))
    elif type(n) is TypeAbstraction:
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(n.type))
    else:
        raise TypeException("Substitution unknown:", n, type(n))


def substitution_type_in_type(n, replacement: Type, replaced):
    """ T[replacement/replaced] """
    r = lambda x: substitution_type_in_type(x, replacement, replaced)
    if type(n) is BasicType:
        if n.name == replaced:
            return replacement
        else:
            return n
    elif type(n) is RefinedType:
        return RefinedType(n.name, r(n.type), n.cond)
    elif type(n) is ArrowType:
        return ArrowType(arg_name=n.arg_name,
                         arg_type=r(n.arg_type),
                         return_type=r(n.return_type))
    elif type(n) is TypeApplication:
        return TypeApplication(target=r(n.target), argument=r(n.argument))
    elif type(n) is TypeAbstraction:
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(n.type))
    else:
        raise TypeException("Substitution unknown:", n, type(n))
