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
    def __init__(self):
        pass
    def __str__(self):
        return "…"
        
class Literal(TypedNode):
    def __init__(self, value, type):
        self.value = value
        self.type = type
    
    def __str__(self):
        return "{}".format(self.value)


class Invocation(TypedNode):
    def __init__(self, name, arguments, version=""):
        self.name = name
        self.arguments = arguments
        self.version = version # Version is for multiversioning
    
    def __str__(self):
        return "{}({})".format(self.name, ", ".join([ str(x) for x in self.arguments ]))
        

class Operator(TypedNode):
    def __init__(self, name, *arguments):
        self.name = name
        self.arguments = arguments
        self.is_unary = len(arguments) == 1
    
       
    def __str__(self):
        if self.is_unary:
            return "{}{}".format(self.name, self.arguments)
        return "({} {} {})".format(self.arguments[0], self.name, self.arguments[1])
        

class Block(TypedNode):
    def __init__(self, *expressions):
        self.expressions = expressions
        
    def __str__(self):
        return "{{ {} }}".format("\n\t\t".join([ str(x) for x in self.expressions ]))
        
        
class Atom(Node):
    def __init__(self, name):
        self.name = name
        
    def __str__(self):
        return "{}".format(self.name)
        
class LambdaExpression(TypedNode):
    def __init__(self, parameters, body):
        self.parameters = parameters
        self.body = body
        
    def __str__(self):
        return "({}) -> {}".format(", ".join([ str(x) for x in self.parameters ]),self.body)
        
        
class Let(TypedNode):
    def __init__(self, name, body, type=None, coerced=False):
        self.name = name
        self.body = body
        self.type = type
        self.coerced = coerced
        
    def __str__(self):
        symb = self.coerced and ":!" or ":"
        return "{} {} {} = {}".format(self.name, symb, self.type, self.body)
        
 
class Argument(TypedNode):
    def __init__(self, name, type, trackedBy=None):
        self.name = name
        self.type = type
        self.trackedBy = trackedBy
        
    def __str__(self):
        tb = self.trackedBy and " trackedBy " + str(self.trackedBy) or ""
        return "{}:{}{}".format(self.name, self.type, tb)


class FunctionDecl(TypedNode):
    def __init__(self,
        name,
        parameters,
        return_value,
        type_parameters = None,
        refinements = None,
        effects = None,
        body = None
        ):
        self.name = name
        self.parameters = parameters or []
        self.return_value = return_value
        self.type_parameters = type_parameters or []
        self.refinements = refinements or []
        self.effects = effects or []
        self.body = body
        self.is_native = body == None

    def __str__(self):
        native = self.is_native and "native " or ""
        type_parameters = ", ".join(map(str, self.type_parameters))
        tpars = type_parameters and type_parameters + " => " or ""
        pars = ", ".join(map(str, self.parameters))
        conds = self.refinements and " where [" + " and ".join(map(str, self.refinements)) + "]" or ""
        effects = self.effects and " with [" + " and ".join(map(str, self.effects)) + "]" or ""
        body = self.body and "{\n\t\t" + str(self.body) + "}" or ""
        return "{}{} : {} ({}) -> {}{}{}{}".format(native, self.name, tpars, pars, str(self.return_value), conds, effects, body)


class TypeDecl(TypedNode):
    def __init__(self, name_imported, alias, properties=None, refinements=None):
        self.type = name_imported
        self.alias = alias
        self.properties = properties or []
        self.refinements = refinements or []
        
    def __str__(self):
        al = self.alias and " as " + str(self.alias) or ""
        conds = self.refinements and " where [" + " and ".join(map(str, self.refinements)) + "]" or ""
        props = self.properties and " { " + "\n".join(map(str, self.properties)) + " }" or ""
        return "type {}{}{}{}".format(str(self.type), props, conds, al)

class Import(Node):
    def __init__(self, name):
        self.name = name
        
    def __str__(self):
        return "import {}".format(self.name)
