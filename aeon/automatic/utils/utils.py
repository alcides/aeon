from aeon.ast import Literal, Var, Hole, If, Application, Abstraction, TApplication, TAbstraction, Definition
from aeon.interpreter import EvaluationContext, run

# =============================================================================
# Builds the evaluation context from the unholed programs
def build_evaluation_context(program):
    
    eval_ctx = EvaluationContext()
    unholed_program = []

    for declaration in program.declarations:
        if isinstance(declaration, Definition):
            if not has_holes(declaration) and declaration.name != 'main':
                run(declaration, eval_ctx)

    return eval_ctx

# Adds a declaration to the evaluation context
def add_evaluation_context(declaration, eval_ctx):
    run(declaration, eval_ctx)


#==============================================================================
# Checks if a certain program has holes in it
def has_holes(node):
    
    if isinstance(node, Hole):
        return True

    elif isinstance(node, Literal):
        return False
    
    elif isinstance(node, Var):
        return False
    
    elif isinstance(node, Definition):
        return has_holes(node.body)
    
    elif isinstance(node, If):
        return has_holes(node.cond) or has_holes(node.then) or \
               has_holes(node.otherwise)
    
    elif isinstance(node, Application):
        return has_holes(node.target) or has_holes(node.argument)
    
    elif isinstance(node, Abstraction):
        return has_holes(node.body)
    
    elif isinstance(node, TAbstraction):
        return has_holes(node.body)
    
    elif isinstance(node, TApplication):
        return has_holes(node.target)

    else:
        raise Exception("Couldnt find the node:", node)