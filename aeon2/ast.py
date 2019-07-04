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


class Hole(TypedNode):
    """ \hole """

    def __init__(self):
        pass

    def __str__(self):
        return "…"


class Literal(TypedNode):
    """ true | false | x """

    def __init__(self, value, type):
        self.value = value
        self.type = type

    def __str__(self):
        return "{}".format(self.value)


class Var(Node):
    """ x """

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return "{}".format(self.name)


class If(TypedNode):
    """ x """

    def __init__(self, cond, then, otherwise):
        self.cond = cond
        self.then = then
        self.otherwise = otherwise

    def __str__(self):
        return "if {} then {} else {}".format(self.cond, self.then,
                                              self.otherwise)


class Application(TypedNode):
    def __init__(self, target, arguments):
        self.target = target
        self.arguments = arguments

    def __str__(self):
        return "{}({})".format(self.target,
                               ", ".join([str(x) for x in self.arguments]))


class Abstraction(TypedNode):
    def __init__(self, parameters, body):
        self.parameters = parameters
        self.body = body

    def __str__(self):
        return "\{} -> {}".format(", ".join([str(x) for x in self.parameters]),
                                  self.body)


class Fix(TypedNode):
    def __init(self):
        pass

    def __str__(self):
        return "fix"


class TAbstraction(TypedNode):
    def __init__(self, typevar, kind, body):
        self.typevar = typevar
        self.kind = kind
        self.body = body

    def __str__(self):
        return "/\{}:{}.({})".format(self.typevar, self.kind, self.body)


class TApplication(TypedNode):
    def __init__(self, expression, type):
        self.expression = expression
        self.type = type

    def __str__(self):
        return "{}[{}]".format(self.expression, self.type)


# Other Structure


class Argument(TypedNode):
    def __init__(self, name, type):
        self.name = name
        self.type = type

    def __str__(self):
        return "{}:{}".format(self.name, self.type)


class Definition(Node):
    def __init__(self, name, type, body):
        self.name = name
        self.type = type
        self.body = body

    def __str__(self):
        return "{} : {} = {}".format(self.name, self.type, self.body)


class TypeAlias(TypedNode):
    def __init__(self, alias, type):
        self.alias = alias
        self.type = type


class Import(Node):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return "import {}".format(self.name)
