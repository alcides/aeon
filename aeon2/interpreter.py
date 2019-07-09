from .types import *
from .ast import *


def run(a: Program):

    ctx = {}

    # Inserir native - talvez fazer modulo para isto
    ctx['+'] = lambda x: lambda y: x + y
    ctx['-'] = lambda x: lambda y: x - y
    ctx['*'] = lambda x: lambda y: x * y
    ctx['/'] = lambda x: lambda y: x / y
    ctx['%'] = lambda x: lambda y: x % y
    ctx['emptyList'] = []

    evaluate(ctx, a)
    print("Interpreter: ", ctx)

def evaluate(ctx, node):

    print(type(node), " :::::::::: ", node)
    nodeType = type(node)

    # Literal
    if nodeType is Literal:
        if type(node.type) is BasicType:
            return convert(node.type.name, node.value)
        elif type(node.type) is RefinedType:
            return convert(node.type.type.name, node.value)
        else:
            print("Literal com tipo invalido.")
    # Var - return the ctx value
    elif nodeType is Var:
        return ctx.get(node.name) # CUIDADO: retorna None para native functions e non-existing functions
    # Program
    elif nodeType is Program:
        for d in node.declarations:
            print(30*'=')
            evaluate(ctx, d)
    # Definition
    elif nodeType is Definition:
        if type(node.body) is Abstraction:
            ctx[node.name] = evaluate(ctx, node.body) # eval(evaluate(ctx, node.body)) # descomentar depois
        else:
            bodyEval = evaluate(ctx, node.body)
            # If it was a native function, it returns None, so we def non-native functions
            if bodyEval is not None:
                ctx[node.name] = bodyEval
    # Hole - nao acontece
    elif nodeType is Hole:
        pass
    # If - Executa a operacao resultado do then
    elif nodeType is If:
        cond = evaluate(ctx, node.cond)
        return cond and evaluate(ctx, node.then) or evaluate(ctx, node.otherwise)
    # Import the statements
    elif nodeType is Import:
        # TODO: o prof tinha dito para passar a frente, mas presumo que tenha de
        # carregar para contexto o que esta no ficheiro  importar
        pass
    elif nodeType is Application:
        # target ~> application, argument ~> Literal or Var

        target = node.target
        argument = node.argument

        print("target: ", type(target), target)
        print("argument: ", type(argument), argument)
        # TODO: On hold
        #targetEval = evaluate(ctx, target)
        #argumentEval = evaluate(ctx, argument) and not None or argument.name

        return "affz" #targetEval(argumentEval)

        print("Application: ", node)
    # Abstraction - retorna representacao em string, convertida
    elif nodeType is Abstraction:
        # criar contexto proprio para abstracoes????
        # node.arg_type ~> basictype, node.arg_name ~>, node.body ~> abstraction
        # print(">>>>>", type(node.body), node.body)
        bodyEval = evaluate(ctx, node.body)
        if bodyEval is None:
            bodyEval = node.body.name
        return "lambda {} : {}".format(node.arg_name, bodyEval)

    elif nodeType is TAbstraction:
        print("TAbstraction: ", node)
    elif nodeType is TApplication:
        print("TApplication: ", node)
    elif nodeType is TypeAlias:
        print("TypeAlias: ", node)
    elif nodeType is TypeDeclaration:
        print("TypeDeclaration: ", node)

    else:
        print("ERROR: ", type(node), node)
        return None

# ------------------------------------------------------------------------------
# Converts the aeon basic value to a python value
def convert(name, value):
    if name == 'Object' or name == 'Void':
        return None  # TODO: confirmar
    if name == 'Boolean':
        return value == "true" and True or False
    elif name == 'Integer':
        return int(value)
    elif name == 'Double':
        return float(value)
    elif name == 'String':
        return node.value
    elif name == 'Bottom':
        return value  # TODO: confirmar
    else:
        print("ERROR: must define the default type: ", node.type)
        return None
# ------------------------------------------------------------------------------
