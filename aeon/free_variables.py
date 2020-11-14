from typing import Any, List

from .types import Type, BasicType, AbstractionType, RefinedType, TypeAbstraction, TypeApplication, \
    UnionType, IntersectionType, ExistentialType

from .ast import Node, Literal, Var, Application, Abstraction, TApplication, TAbstraction

def without(l:list, v:Any):
    return [ x for x in l if x != v ]

def free_variables(n:Node) -> List[str]:
    if isinstance(n, Literal):
        return []
    elif isinstance(n, Var):
        return [n.name]
    elif isinstance(n, Application):
        return free_variables(n.target) + free_variables(n.argument)
    elif isinstance(n, Abstraction):
        return without(free_variables(n.body), n.arg_name)
    elif isinstance(n, TApplication):
        return free_variables(n.target)
    elif isinstance(n, TAbstraction):
        return free_variables(n.body)
    else:
        raise Exception("Missing case in freevars", n, type(n))


def free_variables_in_type(t:Type) -> List[str]:
    if isinstance(t, BasicType):
        return []
    elif isinstance(t, AbstractionType):
        return without(free_variables_in_type(t.return_type), t.arg_name)
    elif isinstance(t, RefinedType):
        return without(free_variables_in_type(t.type) + free_variables(t.cond), t.name)
    elif isinstance(t, TypeAbstraction):
        return free_variables_in_type(t.type) # TODO
    elif isinstance(t, TypeApplication):
        return free_variables_in_type(t.target) + free_variables_in_type(t.argument)
    elif isinstance(t, UnionType):
        return free_variables_in_type(t.left) + free_variables_in_type(t.right)
    elif isinstance(t, IntersectionType):
        return free_variables_in_type(t.left) + free_variables_in_type(t.right)
    elif isinstance(t, ExistentialType):
        return without(free_variables_in_type(t.left) + free_variables_in_type(t.right), t.left_name)
    else:
        raise Exception("Missing case in freevars ty", t, type(t))
