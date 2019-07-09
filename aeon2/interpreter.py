from .types import *
from .ast import *

def run(a: Program):

    # Distincao entre variaveis e funcoes - acho que jah nao eh preciso
    # {name:(type, value)...}
    ctx = {}
    functions = {}

    for node in a:
        eval(node, ctx)

    print("Interpreter: ", ctx)

def eval(node, ctx):

    nodeType = type(node)

    # Literal
    if nodeType is Literal:
        if type(node.type) is BasicType:
            return convert(node.type.name, node.value)
        elif type(node.type) is RefinedType:
            return convert(node.type.type.name, node.value)
        else:
            print("Opsie aqui. Literal com tipo invalido.")
    # Var - return the ctx value
    elif nodeType is Var:
        # TODO: Temp fix - perguntar se coloco funcao implementada em python aqui
        if node.name == "native":
            return "native"
        return ctx[node.name]
    # Definition
    elif nodeType is Definition:
        ctx[node.name] = eval(node.body, ctx)
    # Hole - TODO: Presumo que chamar o automatic
    elif nodeType is Hole:
        pass
    # If - Executa a operacao resultado do then
    elif nodeType is If:
        cond = eval(node.cond, ctx)
        return cond and eval(node.then, ctx) or eval(node.otherwise, ctx)
    # Import the statements
    elif nodeType is Import:
        # TODO: o prof tinha dito para passar a frente, mas presumo que tenha de
        # carregar para contexto o que esta no ficheiro  importar
        pass
    elif nodeType is Application:
        print("Application: ", node)
    elif nodeType is Abstraction:
        print("Abstraction: ", node)
    elif nodeType is TAbstraction:
        print("TAbstraction: ", node)
    elif nodeType is TApplication:
        print("TApplication: ", node)
    elif nodeType is TypeAlias:
        print("TypeAlias: ", node)
    elif nodeType is TypeDeclaration:
        print("TypeDeclaration: ", node)

    else:
        print("ERROR: ", node)

# ----------------------------------------------------------------------
# Converts the aeon basic value to a python value
def convert(name, value):
    if name == 'Object' or name == 'Void':
        return None # TODO: confirmar
    if name == 'Boolean':
        return value == "true" and True or False
    elif name == 'Integer':
        return int(value)
    elif name == 'Double':
        return float(value)
    elif name == 'String':
        return node.value
    elif name == 'Bottom':
        return value # TODO: confirmar
    else:
        print("ERROR: must define the default type: ", node.type)
        return None
# ----------------------------------------------------------------------
