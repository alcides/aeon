import copy
import sys
import random

from typing import Any, Dict, List


class TypeException(Exception):
    def __init__(self,
                 name,
                 description="",
                 given=None,
                 expected=None,
                 *args,
                 **kwargs):
        super(TypeException, self).__init__(name, description)
        self.expected = expected
        self.given = given


global fresh_var_counter
fresh_var_counter = 0


class TypingContext(object):
    def __init__(self):
        self.type_aliases = {}
        self.variables: Dict[str, Type] = {}
        self.type_variables: Dict[str, Kind] = {}
        self.restrictions: List[Any] = []
        self.uninterpreted_functions: Dict[str, Type] = {}
        self.inside_refinement = False

    def setup(self):
        from .libraries.stdlib import get_builtin_variables, get_all_uninterpreted_functions
        for name, type, _ in get_builtin_variables():
            self.variables[name] = type
        for name, type in get_all_uninterpreted_functions():
            self.uninterpreted_functions[name] = type

        self.type_variables = {
            t_v.name: star,
            t_i.name: star,
            t_f.name: star,
            t_o.name: star,
            t_b.name: star,
            t_s.name: star,
            bottom.name: star,
            top.name: star
        }

    def __str__(self):
        wrap = lambda d: ", ".join(
            [str(k) + "=" + str(d[k]) for k in d.keys()])
        return "[type_vars:{}, vars:{}, restrictions:{}, aliases={}]".format(
            wrap(self.type_variables),
            wrap(self.variables),
            ", ".join([str(r) for r in self.restrictions]),
            # wrap(self.uninterpreted_functions),   uninterpreted_functions:{},
            wrap(self.type_aliases),
        )

    def print_ctx(self):
        print("Context")
        print(" Aliases:")
        for al in self.type_aliases:
            print(al, self.type_aliases[al])
        print(" TypeVars:")
        for al in self.type_variables:
            print(al, self.type_variables[al])
        print(" Vars:")
        for al in self.variables:
            print(al, self.variables[al])
        print(" Restrictions:")
        for al in self.restrictions:
            print(al)
        print(".....")

    def copy(self):
        t = TypingContext()
        t.type_aliases = self.type_aliases.copy()
        t.variables = self.variables.copy()
        t.type_variables = self.type_variables.copy()
        t.restrictions = self.restrictions.copy()
        t.uninterpreted_functions = self.uninterpreted_functions.copy()
        return t

    def add_var(self, n, t):
        if isinstance(t, BasicType):
            if t.name in self.type_aliases:
                t = self.type_aliases[t.name]
        self.variables[n] = t

    def enter_refinement(self):
        n = self.copy()
        n.inside_refinement = True
        return n

    def with_uninterpreted(self):
        n = self.enter_refinement()
        for k in n.uninterpreted_functions:
            n.variables[k] = n.uninterpreted_functions[k]
            # I feel like this is a needed change
            n.uninterpreted_functions[k] = n.uninterpreted_functions[k]
        return n

    def add_type_var(self, n, k):
        self.type_variables[n] = k

    def with_var(self, name, type):
        new_ctx = self.copy()
        new_ctx.add_var(name, type)
        return new_ctx

    def with_type_var(self, name, kind):
        new_ctx = self.copy()
        new_ctx.add_type_var(name, kind)
        return new_ctx

    def with_cond(self, c):
        new_ctx = self.copy()
        new_ctx.restrictions.append(c)
        return new_ctx

    def __contains__(self, n):
        return n in self.variables.keys() or n in self.type_variables.keys()

    def fresh_type_var(self):
        global fresh_var_counter
        fresh_var_counter += 1
        k = "_fresh_t_{}".format(fresh_var_counter)
        assert (k not in self.type_variables.keys())
        return k

    def fresh_var(self):
        global fresh_var_counter
        fresh_var_counter += 1
        k = "_fresh_{}".format(fresh_var_counter)
        assert (k not in self)
        return k


class Kind(object):
    def __init__(self, k1=None, k2=None):
        self.k1 = k1
        self.k2 = k2

    def is_star(self):
        return self.k1 == None and self.k2 == None

    def __eq__(self, o):
        if type(o) != Kind:
            return False
        if type(o) == AnyKind:
            return True
        if self.is_star() and o.is_star():
            return True
        return self.k1 == o.k1 and self.k2 == o.k2

    def __repr__(self):
        return str(self)

    def __str__(self):
        if self.is_star():
            return "*"
        return "{} => {}".format(self.k1, self.k2)


class AnyKind(Kind):
    def __init__(self):
        pass

    def __eq__(self, o):
        return type(o) == Kind

    def __str__(self):
        return "Any *"


star = Kind()


class Type(object):
    def copy(self):
        return copy.deepcopy(self)

    def __repr__(self):
        return str(self)


class BasicType(Type):
    """ Integer | Boolean | B """
    def __init__(self, name: str):
        self.name = str(name)

    def __str__(self):
        return self.name

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name

    def __hash__(self):
        return hash(self.name)


class AbstractionType(Type):
    """ x:T -> U """
    def __init__(self, arg_name: str, arg_type: Type, return_type: Type):
        self.arg_name = arg_name
        self.arg_type = arg_type
        self.return_type = return_type

    def __str__(self):
        return "({}:{} -> ({}))".format(self.arg_name, self.arg_type,
                                        self.return_type)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.arg_name == o.arg_name \
            and self.arg_type == o.arg_type \
            and self.return_type == o.return_type


class RefinedType(Type):
    """ x:T where U """
    def __init__(self, name: str, type: Type, cond):  # : Node
        assert(type is not None)
        self.name = name
        self.type = type
        self.cond = cond

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name \
            and self.type == o.type \
            and self.cond == o.cond

    def __str__(self):
        return "{{ {}:{} where {} }}".format(self.name, self.type, self.cond)


class TypeAbstraction(Type):
    """t:k => T"""
    def __init__(self, name: str, kind: Kind, type: Type):
        self.name = name
        self.kind = kind
        self.type = type

    def __str__(self):
        return "({}:{} => {})".format(self.name, self.kind, self.type)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name \
            and self.kind == o.kind \
            and self.type == o.type


class TypeApplication(Type):
    """ T U """
    def __init__(self, target: Type, argument: Type):
        if target == None:
            raise Exception("First none!")
        self.target = target
        self.argument = argument

    def __str__(self):
        return "({} {})".format(self.target, self.argument)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.target == o.target \
            and self.argument == o.argument


class UnionType(Type):
    """ T + U """
    def __init__(self, left: Type, right: Type):
        self.left = left
        self.right = right

    def __str__(self):
        return "({} + {})".format(self.left, self.right)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.left == o.left \
            and self.right == o.right


class IntersectionType(Type):
    """ T & U """
    def __init__(self, left: Type, right: Type):
        self.left = left
        self.right = right

    def __str__(self):
        return "({} & {})".format(self.left, self.right)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.left == o.left \
            and self.right == o.right


class ProductType(Type):
    """ (x:T, U) """
    def __init__(self, left_name: str, left: Type, right: Type):
        self.left_name = left_name
        self.left = left
        self.right = right

    def __str__(self):
        return "({}:{}, {})".format(self.left_name, self.left, self.right)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.left_name == o.left_name \
            and self.left == o.left \
            and self.right == o.right


class ExistentialType(Type):
    """ (∃x:T, U) """
    def __init__(self, left_name: str, left: Type, right: Type):
        self.left_name = left_name
        self.left = left
        self.right = right

    def __str__(self):
        return "(∃{}:{}.{})".format(self.left_name, self.left, self.right)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.left_name == o.left_name \
            and self.left == o.left \
            and self.right == o.right


# defaults
t_v = BasicType('Void')
t_o = BasicType('Object')
t_f = BasicType('Double')
t_i = BasicType('Integer')
t_b = BasicType('Boolean')
t_s = BasicType('String')
bottom = BasicType('Bottom')
top = BasicType('Top')

t_delegate = BasicType("??")



def type_map(pred, f, n):
    rec = lambda n1: type_map(pred, f, n1)
    if pred(n):
        return f(rec, n)
    if isinstance(n, AbstractionType):
        return AbstractionType(n.arg_name, n.arg_type, rec(n.return_type))
    elif isinstance(n, RefinedType):
        return RefinedType(n.name, rec(n.type), n.cond)
    elif isinstance(n, TypeAbstraction):
        return TypeAbstraction(n.name, n.kind, rec(n.type))
    elif isinstance(n, TypeApplication):
        return TypeApplication(rec(n.target), n.argument)
    elif isinstance(n, UnionType):
        return UnionType(rec(n.left), rec(n.right))
    elif isinstance(n, IntersectionType):
        return IntersectionType(rec(n.left), rec(n.right))
    elif isinstance(n, ExistentialType):
        return ExistentialType(n.left_name, n.left, rec(n.right))
    elif isinstance(n, ProductType):
        return ProductType(n.left_name, n.left, n.right)
    return n



def apply_rec(pred, f, n):
    print(" ....> 1. n:", n)
    rec = lambda n1: type_map(pred, f, n1)
    if pred(n):
        return f(rec, n)
    if isinstance(n, AbstractionType):
        return AbstractionType(n.arg_name, rec(n.arg_type), rec(n.return_type))
    elif isinstance(n, RefinedType):
        return RefinedType(n.name, rec(n.type), n.cond)
    elif isinstance(n, TypeAbstraction):
        return TypeAbstraction(n.name, n.kind, rec(n.type))
    elif isinstance(n, TypeApplication):
        return TypeApplication(rec(n.target), n.argument)
    elif isinstance(n, UnionType):
        return UnionType(rec(n.left), rec(n.right))
    elif isinstance(n, IntersectionType):
        return IntersectionType(rec(n.left), rec(n.right))
    elif isinstance(n, ExistentialType):
        return ExistentialType(n.left_name, rec(n.left), rec(n.right))
    elif isinstance(n, ProductType):
        return ProductType(n.left_name, rec(n.left), rec(n.right))
    return n

def find_basic_types(n):
    rec = lambda n1: find_basic_types(n1)
    if isinstance(n, BasicType):
        return [n.name]
    if isinstance(n, AbstractionType):
        return rec(n.return_type)
    elif isinstance(n, RefinedType):
        return rec(n.type)
    elif isinstance(n, TypeAbstraction):
        return [ b for b in rec(n.type) if b != n.name ]
    elif isinstance(n, TypeApplication):
        return rec(n.target) + rec(n.argument)
    elif isinstance(n, UnionType):
        return rec(n.left) + rec(n.right)
    elif isinstance(n, IntersectionType):
        return rec(n.left) + rec(n.right)
    elif isinstance(n, ExistentialType):
        return rec(n.left) + rec(n.right)
    elif isinstance(n, ProductType):
        return rec(n.left) + rec(n.right)
    return n

def shape(n:Type):
    if isinstance(n, BasicType):
        return n
    elif isinstance(n, AbstractionType):
        return AbstractionType(n.arg_name, shape(n.arg_type), shape(n.return_type))
    elif isinstance(n, RefinedType):
        return shape(n.type)
    elif isinstance(n, TypeApplication) and isinstance(n.target, TypeAbstraction):
        return shape(n.target.type)
    elif isinstance(n, TypeApplication):
        return TypeApplication(shape(n.target), shape(n.argument))
    elif isinstance(n, TypeAbstraction):
        return TypeAbstraction(n.name, n.kind, shape(n.type))
    elif isinstance(n, UnionType):
        return UnionType(shape(n.left), shape(n.right))
    elif isinstance(n, IntersectionType):
        return IntersectionType(shape(n.left), shape(n.right))
    elif isinstance(n, ProductType):
        return ProductType(n.left_name, shape(n.left), shape(n.right))
    elif isinstance(n, ExistentialType):
        return shape(n.right)
    else:
        raise Exception("Missing case in shape")
