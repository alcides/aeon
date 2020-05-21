from aeon.ast import *
from aeon.types import *

def deducer(ast, context, holed):

    for declaration, holes in holed:
        context = HoleContext(context.copy())
        deduce(context, declaration)

    return ast, context, holed

# =============================================================================
# Hole context
class HoleContext(object):

    def __init__(self, context):
        self.context = context
        self.stack = list()

    def copy(self):
        result = HoleContext(self.context.copy())
        result.stack = self.stack.copy()
        return result
    
    def with_type(self, typee):
        new_ctx = self.copy()
        new_ctx.stack.append(typee)
        return new_ctx 
    
    def pop_type(self):
        return self.stack[-1]    

    def with_tapp(self, T, typee):
        new_ctx = self.copy()
        new_ctx.context.type_aliases[T] = typee
        return new_ctx
    
    def with_var(self, n, typee):
        new_ctx = self.copy()
        new_ctx.context.variables[n] = typee
        return new_ctx
        

# =============================================================================
# Hole Deducer
# Hole
def deduce_hole(context, node):
    node.type = context.pop_type()
        
# Definition
def deduce_definition(context, node : Definition):
    deduce(context.with_type(node.return_type), node.body)

# Literal
def deduce_literal(context, node: Literal):
    # Does nothing
    pass

# Variable
def deduce_var(context, node: Var):
    # Does nothing
    pass

# If
def deduce_if(context, node: If):

    # Try to deduce the condition
    if node.cond.type is bottom:
        self.hole_stack.append(t_b)
    
    self.deduce(node.cond)
    
    # If the otherwise is a hole
    if node.otherwise.type is bottom:
        self.hole_stack.append(node.type)
    
    self.deduce(node.then)

    # If the then is a hole
    if node.then.type is bottom:
        self.hole_stack.append(node.type)
    
    self.deduce(node.otherwise)

# Application
def deduce_application(context, node: Application):
    deduce(context, node.target)
    deduce(context.with_type(node.target.arg_type), node.argument)

# Abstraction
def deduce_abstraction(context, node: Abstraction):
    deduce(context.with_var(node.arg_name, node.arg_type), node.body)

# TAbstraction
def deduce_tabstraction(context, node: TAbstraction):
    pass

# TApplication
def deduce_tapplication(context, node: TApplication):
    pass

# Dispatcher
def deduce(context, node):
    gen_tabs()
    if isinstance(node, Hole):
        deduce_hole(context, node)
    elif isinstance(node, Literal):
        deduce_literal(context, node)
    elif isinstance(node, Var):
        deduce_var(context, node)
    elif isinstance(node, If):
        deduce_if(context, node)
    elif isinstance(node, Application):
        deduce_application(context, node)
    elif isinstance(node, Abstraction):
        deduce_abstraction(context, node)
    elif isinstance(node, Definition):
        deduce_definition(context, node)
    elif isinstance(node, TAbstraction):
        deduce_tabstraction(context, node)
    elif isinstance(node, TApplication):
        deduce_tapplication(context, node)
    else:
        raise Exception("Unknown type of node: ", type(node))

# =============================================================================
# Auxiliary methods
counter = 0

def gen_tabs():
    name = '_T{}'.format(counter)
    typee = TypeAbstraction(name, star, BasicType(name))
    counter += 1
    TAbstraction(name, star, Hole(BasicType(name)))

'''
inferencia com unificador
program(x : Integer, y : Double) :: String {
    (T2 : * => [T2 -> Top]([T2])) [];
    
    "qualquercoisa";
}

'''