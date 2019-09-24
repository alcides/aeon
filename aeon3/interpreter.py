from .types import *
from .ast import *
from .stdlib import *


def run(a: Program):
 
    ctx = nativeFunctions()
    evaluate(ctx, a)

def evaluate(ctx, node):
    
    # print(node)
    nodeType = type(node)

    # Literal
    if nodeType is Literal:
        return node.value
    # Var - return the ctx value
    elif nodeType is Var:
        return ctx.get(
            node.name
        )  # CUIDADO: retorna None para native functions e non-existing functions
    # Program
    elif nodeType is Program:
        for d in node.declarations:
            evaluate(ctx, d)
    # Definition
    elif nodeType is Definition:
        if type(node.body) is Var:
            bodyEval = evaluate(ctx, node.body)
            # If it was ... = native, it returns None, so we only define non-native functions
            if bodyEval is not None:
                ctx[node.name] = bodyEval
        else:
            ctx[node.name] = evaluate(ctx, node.body)
    # Hole - nao acontece
    elif nodeType is Hole:
        pass
    # If - Executa a operacao resultado do then
    elif nodeType is If:
        cond = evaluate(ctx, node.cond)
        return cond and evaluate(ctx, node.then) or evaluate(
            ctx, node.otherwise)
    # Import - never happens
    elif nodeType is Import:
        pass
    elif nodeType is Application:
        # target ~> abstraction or application or var, argument ~> Literal or Var
        target = evaluate(ctx, node.target)
        if node.argument is None:
            argument = 0 # TODO:
        else:
            argument = evaluate(ctx, node.argument)
        #print(node.target, target)
        #print(argument, node.argument)
        return target(argument)
    # Abstraction - retorna representacao em string, convertida
    elif nodeType is Abstraction:
        # criar contexto proprio para abstracoes, a experimentar
        newCtx = ctx.copy()
        return lambda x: evaluate(ctxPut(newCtx, node.arg_name, x), node.body)
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


## HELPER


def ctxPut(ctx, varName, var):
    if not varName.name.startswith('_'):
        ctx[varName.name] = var
    return ctx


def nativeFunctions():
    " Builds the context with the native functions "
    ctx = {}
    for name in get_all_builtins():
        ctx[name] = get_builtin_value(name)
    return ctx
