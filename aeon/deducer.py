from aeon.ast import *
from aeon.types import *

from aeon.typechecker.type_simplifier import reduce_type
from aeon.typechecker.bounds import lub


def deducer(ast, context, holed):

    for declaration, holes in holed:
        ctx = DeduceContext(context.copy())
        deduce(ctx, declaration)

    return ast, context, holed


# =============================================================================
# Deduce context
class DeduceContext(object):
    def __init__(self, context):
        self.context = context
        self.stack = list()

    def copy(self):
        result = DeduceContext(self.context.copy())
        result.stack = self.stack.copy()
        return result

    def with_type(self, typee):
        new_ctx = self.copy()
        new_ctx.stack.append(typee)
        return new_ctx

    def pop_type(self):
        return self.stack.pop()

    def head_stack(self):
        return self.stack[-1]

    def is_empty(self):
        return len(self.stack) == 0

    def with_tapp(self, T, typee):
        new_ctx = self.copy()
        new_ctx.context.type_aliases[T] = typee
        return new_ctx

    def contains_tapp(self, T):
        return T in self.context.type_aliases

    def get_tapp(self, T):
        return self.context.type_aliases[T]

    def with_var(self, n, typee):
        new_ctx = self.copy()
        new_ctx.context.variables[n] = typee
        return new_ctx


# =============================================================================
# Hole Deducer


# Hole
def deduce_hole(context, node):

    # If it already has a type, return it
    if node.type != bottom:
        return node.type

    typees = list()

    while not context.is_empty() and isinstance(context.head_stack(),
                                                TypeAbstraction):
        typees.append(context.pop_type())

    assert (not context.is_empty())

    T = context.pop_type()

    # if isinstance(T, BasicType) and context.contains_tapp(T.name):
    #    T = get_tapp(T.name)

    # Englobe in TypeAbstractions
    for ttype in reversed(typees):
        ttype = ttype.copy()
        ttype.type = T
        T = ttype

    node.type = T

    return node.type


# Definition
def deduce_definition(context, node: Definition):
    return deduce(context.with_type(node.return_type), node.body)


# Literal
def deduce_literal(context, node: Literal):
    return node.type


# Variable
def deduce_var(context, node: Var):
    return node.type


# If
def deduce_if(context, node: If):

    ty_cond = deduce(context.with_type(t_b), node.cond)

    # If both have holes at the end
    if node.then.type == bottom and node.otherwise.type == bottom:
        ty_then = deduce(context.copy(), node.then)
        ty_otherwise = deduce(context.with_type(ty_then), node.otherwise)

    # If only the then have a hole at the end
    elif node.then.type == bottom:
        ty_then = deduce(context.with_type(node.otherwise.type), node.then)
        ty_otherwise = deduce(context.copy(), node.otherwise)

    # If only the otherwise have a hole at the end
    elif node.otherwise.type == bottom:
        ty_then = deduce(context.copy(), node.then)
        ty_otherwise = deduce(context.with_type(node.then.type),
                              node.otherwise)

    # If none of them is a hole
    else:
        ty_then = deduce(context.copy(), node.then)
        ty_otherwise = deduce(context.copy(), node.otherwise)

    node.cond.type = ty_cond
    node.then.type = ty_then
    node.otherwise.type = ty_otherwise

    node.type = lub(ty_then, ty_otherwise)

    return node.type


# Application
def deduce_application(context, node: Application):

    # TODO: need to set the node.type somewhere in here

    # Check if it is a statement
    if isinstance(node.target, Abstraction) and (node.target.arg_type == top or
                                                 node.target.arg_name == '_'):

        new_ctx = context.with_type(top)
        new_ctx = new_ctx.with_var(node.target.arg_name, node.target.arg_type)

        # Deduce the current statement
        deduce(new_ctx, node.argument)

        # Deduce the next statement
        deduce(context, node.target.body)

    else:
        # Check if target and argument are holes
        if node.target.type == bottom and node.argument.type == bottom:

            tabs = generate_TAbs()

            new_typee = AbstractionType('_', BasicType(tabs.name),
                                        context.head_stack())

            # Create the new context
            new_ctx = context.copy()
            new_ctx.pop_type()
            new_ctx = new_ctx.with_type(new_typee).with_type(tabs)

            ty_target = deduce(new_ctx, node.target)
            ty_argument = deduce(context.with_type(tabs), node.argument)

        # If only the target is a hole
        elif node.target.type == bottom:
            arg_type = node.argument.type

            # Needed to ensure a generalized function
            if isinstance(node.argument, Literal):
                arg_type = reduce_type(context, arg_type)

            return_type = context.pop_type()
            new_typee = AbstractionType('_', arg_type, return_type)

            new_context = context.with_type(new_typee)

            ty_target = deduce(new_context, node.target)
            ty_argument = deduce(context, node.argument)

        # If only the argument is a hole
        elif node.argument.type == bottom:
            new_ctx = context.with_type(node.target.type.arg_type)
            new_ctx = new_ctx.with_var(node.target.type.arg_name,
                                       node.target.type.arg_type)

            ty_target = deduce(context, node.target)
            ty_argument = deduce(new_ctx, node.argument)

        # None of them is a hole
        else:
            ty_target = deduce(context, node.target)
            ty_argument = deduce(context, node.argument)

    return node.type


# Abstraction
def deduce_abstraction(context, node: Abstraction):
    ty_abs = deduce(context.with_var(node.arg_name, node.arg_type), node.body)
    node.type = AbstractionType(node.arg_name, node.arg_type, ty_abs)
    return node.type


# TAbstraction
def deduce_tabstraction(context, node: TAbstraction):
    ty_tabs = deduce(context, node.body)
    node.type = TypeAbstraction(node.typevar, node.kind, ty_tabs)
    return node.type


# TApplication
def deduce_tapplication(context, node: TApplication):
    T = BasicType(node.target.type.name)
    U = node.argument

    ty_tapp = deduce(context.with_tapp(T, U), node.target)
    node.type = TypeApplication(ty_tapp, node.argument)

    return node.type


# Dispatcher
def deduce(context, node):

    if isinstance(node, Hole):
        return deduce_hole(context, node)

    elif isinstance(node, Literal):
        return deduce_literal(context, node)

    elif isinstance(node, Var):
        return deduce_var(context, node)

    elif isinstance(node, If):
        return deduce_if(context, node)

    elif isinstance(node, Application):
        return deduce_application(context, node)

    elif isinstance(node, Abstraction):
        return deduce_abstraction(context, node)

    elif isinstance(node, Definition):
        return deduce_definition(context, node)

    elif isinstance(node, TAbstraction):
        return deduce_tabstraction(context, node)

    elif isinstance(node, TApplication):
        return deduce_tapplication(context, node)

    else:
        raise Exception("Unknown type of node: ", type(node))


# =============================================================================
# Auxiliary methods
counter = 0


def generate_TAbs():
    global counter
    counter += 1
    name = '_T{}'.format(counter)
    return TypeAbstraction(name, star, None)


'''
inferencia com unificador
program(x : Integer, y : Double) :: String {
    [T2 : * => (T2 -> Top)]([T2 : * => T2]);

    "qualquercoisa";
}

'''
