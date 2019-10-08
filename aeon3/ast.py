class Node(object):
    pass


class Program(Node):
    def __init__(self, declarations):
        self.declarations = declarations

    def __str__(self):
        return "".join(map(lambda x: "{}\n".format(x), self.declarations))


class TypedNode(Node):
    def __init__(self):
        self.type = None

    def with_type(self, t):
        self.type = t
        return self


class Hole(TypedNode):
    """ hole """

    def __init__(self, type):
        super(Hole, self).__init__()
        self.type = type

    def __str__(self):
        return "[[{}]]".format(self.type)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.type == o.type


class Literal(TypedNode):
    """ true | false | 0 | 0.0 """

    def __init__(self, value, type):
        super(Literal, self).__init__()
        self.value = value
        self.type = type

    def __str__(self):
        return "{}".format(self.value)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.value == o.value


class Var(TypedNode):
    """ x """

    def __init__(self, name):
        super(Var, self).__init__()
        self.name = name

    def __str__(self):
        return "{}".format(self.name)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name


class If(TypedNode):
    """ if cond then e else e """

    def __init__(self, cond, then, otherwise):
        super(If, self).__init__()
        self.cond = cond
        self.then = then
        self.otherwise = otherwise

    def __str__(self):
        return "if {} then {} else {}".format(self.cond, self.then,
                                              self.otherwise)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.cond == o.cond \
            and self.then == o.then \
            and self.otherwise == o.otherwise


empty_argument = None

class Application(TypedNode):
    """  e(e) """

    def __init__(self, target, argument):
        # Trying to Application(target, None) is the same as a call with no arguments
        super(Application, self).__init__()
        self.target = target
        self.argument = argument

    def __str__(self):
        return "{}({})".format(self.target, self.argument)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.target == o.target \
            and self.argument == o.argument


class Abstraction(TypedNode):
    """ \\x:T -> e """

    def __init__(self, arg_name, arg_type, body):
        super(Abstraction, self).__init__()
        self.arg_name = arg_name
        self.arg_type = arg_type
        self.body = body

    def __str__(self):
        return "\{}:{} -> {}".format(self.arg_name, self.arg_type, self.body)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.arg_name == o.arg_name \
            and self.arg_type == o.arg_type \
            and self.body == o.body


class TAbstraction(TypedNode):
    """ T:k => e """

    def __init__(self, typevar, kind, body):
        super(TAbstraction, self).__init__()
        self.typevar = typevar
        self.kind = kind
        self.body = body

    def __str__(self):
        return "{}:{} => ({})".format(self.typevar, self.kind, self.body)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.typevar == o.typevar \
            and self.kind == o.kind \
            and self.body == o.body


class TApplication(TypedNode):
    """ e[T] """

    def __init__(self, target, argument):
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
    def __init__(self, name, type, body):
        self.name = name
        self.type = type
        self.body = body

    def __str__(self):
        return "{} : {} = {}".format(self.name, self.type, self.body)


class TypeAlias(Node):
    def __init__(self, name, type):
        self.name = name
        self.type = type

    def __str__(self):
        return "type {} = {}".format(self.name, self.type)


class TypeDeclaration(Node):
    def __init__(self, name, kind, parameters):
        self.name = name
        self.kind = kind
        self.parameters = parameters

    def __str__(self):
        return "type {} {} : {}".format(self.name, self.parameters, self.kind)


class Import(Node):
    def __init__(self, name, function=None):
        self.name = name
        self.function = function

    def __str__(self):
        result = 'import {}'.format(self.name)
        if self.function is not None:
            result = 'import {} from {}'.format(self.function, self.name)
        return result
