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
    """ \hole """

    def __init__(self):
        super(Hole, self).__init__()

    def __str__(self):
        return "…"


class Literal(TypedNode):
    """ true | false | i """

    def __init__(self, value, type):
        super(Literal, self).__init__()
        self.value = value
        self.type = type

    def __str__(self):
        return "{}".format(self.value)


class Var(TypedNode):
    """ x """

    def __init__(self, name):
        super(Var, self).__init__()
        self.name = name

    def __str__(self):
        return "{}".format(self.name)


class If(TypedNode):
    """ if cond then e else e """

    # int a = (a > b) ? 1 : 0;
    #inteiro = True and "ola" or "adeus"

    def __init__(self, cond, then, otherwise):
        super(If, self).__init__()
        self.cond = cond
        self.then = then
        self.otherwise = otherwise

    def __str__(self):
        return "if {} then {} else {}".format(self.cond, self.then,
                                              self.otherwise)


class Application(TypedNode):
    """  e(e) """

    def __init__(self, target, argument):
        super(Application, self).__init__()
        self.target = target
        self.argument = argument

    def __str__(self):
        return "{}({})".format(self.target, self.argument)


class Abstraction(TypedNode):
    """ \\x:T -> e """

    def __init__(self, arg_name, arg_type, body):
        super(Abstraction, self).__init__()
        self.arg_name = arg_name
        self.arg_type = arg_type
        self.body = body

    def __str__(self):
        return "\{}:{} -> {}".format(self.arg_name, self.arg_type, self.body)


class TAbstraction(TypedNode):
    """ T:k => e """

    def __init__(self, typevar, kind, body):
        super(TAbstraction, self).__init__()
        self.typevar = typevar
        self.kind = kind
        self.body = body

    def __str__(self):
        return "{}:{} => ({})".format(self.typevar, self.kind, self.body)


class TApplication(TypedNode):
    """ e[T] """

    def __init__(self, target, argument):
        super(TApplication, self).__init__()
        self.target = target
        self.argument = argument

    def __str__(self):
        return "{}[{}]".format(self.target, self.argument)


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
    def __init__(self, name, kind):
        self.name = name
        self.kind = kind

    def __str__(self):
        return "type {} : {}".format(self.name, self.kind)


class Import(Node):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return "import {}".format(self.name)
