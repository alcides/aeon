import copy

from typing import Any, Optional, List

from aeon.types import RefinedType, Type, Kind, t_i


class Node(object):
    def copy(self):
        return copy.deepcopy(self)

    def __repr__(self):
        return str(self)


class Program(Node):
    def __init__(self, declarations):
        self.declarations = declarations

    def __str__(self):
        return "".join(map(lambda x: "{}\n".format(x), self.declarations))


class TypedNode(Node):
    def __init__(self, t=None):
        self.type = t

    def copy(self):
        return copy.deepcopy(self)

    def __repr__(self):
        return str(self)

    def with_type(self, t: Type):
        self.type = t
        return self

    def get_height(self):
        if hasattr(self, "height"):
            return self.height
        return None


class Hole(TypedNode):
    """ \hole """
    def __init__(self, type: Type):
        super(Hole, self).__init__()
        self.type = type

    def __str__(self):
        return "[[{}]]".format(self.type)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.type == o.type


class Literal(TypedNode):
    """ true | false | 0 | 0.0 """
    def __init__(self, value, type: Type, ensured=False):
        super(Literal, self).__init__(t=type)
        self.value = value
        self.ensured = ensured  # Used to track if needs type validation or not

    def __str__(self):
        if type(self.value) == str:
            return "\"{}\"".format(self.value)
        else:
            return "{}".format(self.value)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.value == o.value


class Var(TypedNode):
    """ x """
    def __init__(self, name: str):
        super(Var, self).__init__()
        self.name = name

    def __str__(self):
        return "{}".format(self.name)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name


class If(TypedNode):
    """ if cond then e else e """
    def __init__(self, cond: TypedNode, then: TypedNode, otherwise: TypedNode):
        super(If, self).__init__()
        self.cond = cond
        self.then = then
        self.otherwise = otherwise

    def __str__(self):
        return "(if {} then {} else {})".format(self.cond, self.then,
                                                self.otherwise)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.cond == o.cond \
            and self.then == o.then \
            and self.otherwise == o.otherwise


class Application(TypedNode):
    """  e(e) """
    def __init__(self, target: TypedNode, argument: TypedNode):
        super(Application, self).__init__()
        self.target = target
        self.argument = argument

    def __str__(self):
        if isinstance(self.target, Application) and isinstance(self.target.target, Var) \
            and not self.target.target.name.isalnum():
            return "({} {} {})".format(self.target.argument,
                                       self.target.target, self.argument)
        if isinstance(self.target, Var) and \
            not self.target.name.isalnum():
            return "({} {})".format(self.target.target, self.argument)
        return "({} {})".format(self.target, self.argument)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.target == o.target \
            and self.argument == o.argument


class Abstraction(TypedNode):
    """ \\x:T -> e """
    def __init__(self, arg_name: str, arg_type: Type, body: TypedNode):
        super(Abstraction, self).__init__()
        self.arg_name = arg_name
        self.arg_type = arg_type
        self.body = body

    def __str__(self):
        return "(\{}:{} -> {})".format(self.arg_name, self.arg_type, self.body)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.arg_name == o.arg_name \
            and self.arg_type == o.arg_type \
            and self.body == o.body


class TAbstraction(TypedNode):
    """ \\T:k => e """
    def __init__(self, typevar: str, kind: Kind, body: TypedNode):
        super(TAbstraction, self).__init__()
        self.typevar = typevar
        self.kind = kind
        self.body = body

    def __str__(self):
        return "({}:{} => ({}))".format(self.typevar, self.kind, self.body)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.typevar == o.typevar \
            and self.kind == o.kind \
            and self.body == o.body


class TApplication(TypedNode):
    """ e[T] """
    def __init__(self, target: TypedNode, argument: Type):
        super(TApplication, self).__init__()
        self.target = target
        self.argument = argument

    def __str__(self):
        return "{}[{}]".format(self.target, self.argument)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.target == o.target \
            and self.argument == o.argument


# Other Structure


class Definition(Node):
    def __init__(self,
                 name: str,
                 type: Type,
                 body: TypedNode,
                 return_type: Optional[Type] = None):
        self.name = name
        self.type = type
        self.body = body
        self.return_type = return_type

    def __str__(self):
        return "{} : {} = {}".format(self.name, self.type, self.body)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name \
            and self.type == o.type \
            and self.body == o.body \
            and self.return_type == o.return_type


class TypeAlias(Node):
    def __init__(self, name: str, type: Type):
        self.name = name
        self.type = type

    def __str__(self):
        return "type {} = {}".format(self.name, self.type)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name \
            and self.type == o.type


class TypeDeclaration(Node):
    def __init__(self, name: str, kind: Kind, ghost_variables):
        self.name = name
        self.kind = kind
        self.ghost_variables = ghost_variables

    def __str__(self):
        return "type {} : {}".format(self.name, self.kind)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name \
            and self.kind == o.kind \


class Import(Node):
    def __init__(self, name: str, function: Optional[str] = None):
        self.name = name
        self.function = function

    def __str__(self):
        result = 'import {}'.format(self.name)
        if self.function is not None:
            result = 'import {} from {}'.format(self.function, self.name)
        return result

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name \
            and self.function == o.function


def refined_value(v, t, label="_v"):
    if t == None:
        raise Exception("No Type Defined")
    if type(v) == str:
        app1 = Application(Var("smtEq"),
                           Application(Var("String_size"), Var(label)))
        app2 = Application(app1, Literal(len(v), t_i, ensured=True))
        return RefinedType(label, t, app2)
    else:
        app1 = Application(Var("smtEq"), Var(label))
        app2 = Application(app1, Literal(v, type=t))
        return RefinedType(label, t, app2)
