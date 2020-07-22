from aeon.ast import Literal, Var, Hole, If, Application, Abstraction, TApplication, TAbstraction, Definition
from aeon.types import RefinedType, t_b
from aeon.synthesis.utils import filter_refinements
from aeon.interpreter import EvaluationContext, run


#==============================================================================
# Preprocess the holes to only their types and remove non-restricted refinement
def preprocess_holed(holed):

    result = list()

    for declaration, holes in holed:
        
        new_holes = list()

        for ctx, hole in holes:
            T = hole.type

            new_hole = (ctx, T)
            
            if isinstance(T, RefinedType):
                conditions = filter_refinements(ctx, T.name, T.cond)

                if conditions is None:
                    new_hole = (ctx, T.type)
                else:
                    T.cond = conditions
                    
            new_holes.append(new_hole)

        result.append((declaration, new_holes))

    return result


# =============================================================================
# Builds the evaluation context from the unholed programs
def build_evaluation_context(program):

    eval_ctx = EvaluationContext()
    unholed_program = []

    for declaration in program.declarations:
        if isinstance(declaration, Definition):
            if (not has_holes(declaration)) and declaration.name != 'main' and \
               (not isinstance(declaration.body, Var)):
                run(declaration, eval_ctx)

    return eval_ctx


# Adds a declaration to the evaluation context
def add_evaluation_context(declaration, eval_ctx):
    run(declaration, eval_ctx)


# =============================================================================
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

# =============================================================================
def treattype(hole_type, tree, subtree):

    result = subtree.type

    if isinstance(subtree, Literal):
        
        if isinstance(tree, Literal):
            result = hole_type

        elif isinstance(tree, If):
            if tree.cond == subtree:
                result = tree.cond.type
            elif tree.then == subtree:
                result = tree.then.type
            elif tree.otherwise == subtree:
                result = tree.otherwise.type

        elif isinstance(tree, Application):
            if tree.target == subtree:
                result = tree.target.type
            elif tree.argument == subtree:
                result = tree.target.type.arg_type
            
        elif isinstance(tree, Abstraction):
            result = tree.body.type

        elif isinstance(tree, TAbstraction):
            result = tree.body.type
            
        elif isinstance(tree, TApplication):
            result = tree.target.type

        else:            
            raise Exception("Couldnt find the tree when treating:", tree)

    return result