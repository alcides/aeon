from .types import *
from .ast import *
from .libraries.stdlib import *

from multipledispatch import dispatch


def run(node):
    ctx = nativeFunctions()
    return evaluate(ctx, node)


@dispatch(dict, Literal)
def evaluate(ctx, node):
    return node.value


@dispatch(dict, Var)
def evaluate(ctx, node):
    # CUIDADO: retorna None para native functions e non-existing functions
    return ctx.get(node.name)


@dispatch(dict, Program)
def evaluate(ctx, node):
    for declaration in node.declarations:
        evaluate(ctx, declaration)


@dispatch(dict, Definition)
def evaluate(ctx, node):
    if type(node.body) is Var:
        pass
        ''' TODO: confirmar esta remocao
        bodyEval = evaluate(ctx, node.body)
        print(">>>>>>", bodyEval)
        # If it was ... = native, it returns None, so we only define non-native functions
        if bodyEval is not None:
            ctx[node.name] = bodyEval
        '''
    else:
        ctx[node.name] = evaluate(ctx, node.body)


@dispatch(dict, Hole)
def evaluate(ctx, node):
    pass


@dispatch(dict, If)
def evaluate(ctx, node):
    cond = evaluate(ctx, node.cond)
    return evaluate(ctx, node.then) if cond else evaluate(ctx, node.otherwise)


@dispatch(dict, Import)
def evaluate(ctx, node):
    pass


@dispatch(dict, Application)
def evaluate(ctx, node):
    target = evaluate(ctx, node.target)
    if node.argument is None:
        argument = 0  # TODO:
    else:
        argument = evaluate(ctx, node.argument)
    # print("Target: ", node.target, target)
    # print("Argument: ", argument, node.argument)
    return target(argument)


@dispatch(dict, Abstraction)
def evaluate(ctx, node):
    return lambda x: evaluate(ctxPut(ctx.copy(), node.arg_name, x), node.body)


@dispatch(dict, TAbstraction)
def evaluate(ctx, node):
    return evaluate(ctx, node.body)


@dispatch(dict, TApplication)
def evaluate(ctx, node):
    return evaluate(ctx, node.target)


@dispatch(dict, TypeAlias)
def evaluate(ctx, node):
    pass


@dispatch(dict, TypeDeclaration)
def evaluate(ctx, node):
    pass


@dispatch(object, object)
def evaluate(ctx, node):
    raise Exception('Unknown node during evaluation:', type(node), node)


# -----------------------------------------------------------------------------
# ---------------------------------------------------------------------- HELPER


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
