from .types import *
from .ast import *


def run(a: Program):

    ctx = nativeFunctions()
    evaluate(ctx, a)
    print("Interpreter: ", ctx)

def evaluate(ctx, node):

    print(type(node), " :::::::::: ", node)
    nodeType = type(node)

    # Literal
    if nodeType is Literal:
        return node.value
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
            # If it was ... = native, it returns None, so we def non-native functions
            if bodyEval is not None:
                ctx[node.name] = bodyEval
    # Hole - nao acontece
    elif nodeType is Hole:
        pass
    # If - Executa a operacao resultado do then
    elif nodeType is If:
        cond = evaluate(ctx, node.cond)
        return cond and evaluate(ctx, node.then) or evaluate(ctx, node.otherwise)
    # Import - do later
    elif nodeType is Import:
        pass
    elif nodeType is Application:
        # target ~> application or var, argument ~> Literal or Var
        target = evaluate(ctx, node.target)
        argument = evaluate(ctx, node.argument)

        # Returns none if in abstraction context and var doesnt exist
        if argument is None:
            return "({})({})".format(target, node.argument.name)

        if isinstance(target, str):
            target = eval(target)

        return target(argument)
    # Abstraction - retorna representacao em string, convertida
    elif nodeType is Abstraction:
        # criar contexto proprio para abstracoes, a experimentar
        ctx = nativeFunctions()
        bodyEval = evaluate(ctx, node.body)
        return "lambda {} : {}".format(node.arg_name, bodyEval)
    # TAbstraction - avaliar o corpo
    elif nodeType is TAbstraction:
        return evaluate(ctx, node.body)
    # TApplication -
    elif nodeType is TApplication:
        return evaluate(ctx, node.target)
    # TypeAlias - do later
    elif nodeType is TypeAlias:
        pass
    # TypeDeclaration - do later
    elif nodeType is TypeDeclaration:
        pass
    else:
        print("ERROR: ", type(node), node)
        return None

#-------------------------------------------------------------------------------
# Builds the context with the native functions
def nativeFunctions():

    ctx = {}

    # Inserir native - talvez fazer modulo para isto
    ctx['+'] = 'lambda x: lambda y: x + y'
    ctx['-'] = 'lambda x: lambda y: x - y'
    ctx['*'] = 'lambda x: lambda y: x * y'
    ctx['/'] = 'lambda x: lambda y: x / y'
    ctx['%'] = 'lambda x: lambda y: x % y'
    ctx['fix'] = 'lambda x : lambda a : a' # TODO: confirmar
    ctx['print'] = print
    ctx['emptyList'] = []

    return ctx

# ------------------------------------------------------------------------------
