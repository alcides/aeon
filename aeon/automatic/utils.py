from aeon.ast import Var, Abstraction, Application, TApplication, TAbstraction, Hole, Literal, If, Definition
from aeon.types import *

# Generate the and expressions for the typee
def generate_expressions(condition):
    if isinstance(condition.target, Var):
        if condition.target.name == 'And':
            return generate_expressions(condition.argument)
        else:
            return [condition]
    elif isinstance(condition.target, Abstraction):
        return [condition]
    elif isinstance(condition.target, Application):
        if isinstance(condition.target.target, Var):
            if condition.target.target.name == 'And':
                return generate_expressions(condition.argument) +\
                       generate_expressions(condition.target.argument)
        return [condition]
    elif isinstance(condition.target, TApplication):
        return generate_expressions(condition.target)
    elif isinstance(condition.target, TAbstraction):
        return generate_expressions(condition.body)
    else:
        raise Exception("Unknown during and expression generation: ",
                        type(condition), condition)
        return None


# Generate the abstractions so I can englobe the and expressions
def generate_abstractions(definition):
    typee = definition.type
    first_abstraction = Abstraction(typee.arg_name, typee.arg_type,
                                    None)  # None on purpose
    abstraction = first_abstraction
    typee = typee.return_type

    # Add the parameters
    while typee != definition.return_type:
        if not typee.arg_name.startswith("_"):
            abstraction.body = Abstraction(typee.arg_name, typee.arg_type,
                                           None)
            abstraction = abstraction.body
        typee = typee.return_type

    # Add the return
    if isinstance(typee, BasicType):
        pass
    elif isinstance(typee, AbstractionType):
        abstraction.body = Abstraction(typee.arg_name, typee.arg_type, None)
        abstraction = abstraction.body
    elif isinstance(typee, RefinedType):
        abstraction.body = Abstraction(typee.name, typee.type, None)
        abstraction = abstraction.body
    else:
        print("Opsie in generate_abstractions", typee, type(typee))
        sys.exit(-1)

    return first_abstraction, abstraction

def filter_dependent_types(eval_ctx, and_expressions):
    def is_dependent_type(node):
        if isinstance(node, Hole):
            return False
        elif isinstance(node, Literal):
            return False
        elif isinstance(node, Var):
            import aeon.libraries.stdlib as stdlib
            if not stdlib.is_builtin(node.name) and node.name in eval_ctx.ctx:
                return True
            return False
        elif isinstance(node, If):
            return is_dependent_type(node.cond) or\
                   is_dependent_type(node.then) or\
                   is_dependent_type(node.otherwise)
        elif isinstance(node, Application):
            return is_dependent_type(node.target) or\
                   is_dependent_type(node.argument)
        elif isinstance(node, Abstraction):
            return is_dependent_type(node.body)
        elif isinstance(node, TAbstraction):
            return is_dependent_type(node.body)
        elif isinstance(node, TApplication):
            return is_dependent_type(node.target)
        else:
            raise Exception("Couldnt find the node", node)
    
    result = []

    for expression in and_expressions:
        if is_dependent_type(expression):
            result.append(expression)

    return result

# =============================================================================
# ============================================= TEMP - GOING TO BE REMOVED SOON
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
        return has_holes(node.cond) or has_holes(node.then) or has_holes(
            node.otherwise)
    elif isinstance(node, Application):
        return has_holes(node.target) or has_holes(node.argument)
    elif isinstance(node, Abstraction):
        return has_holes(node.body)
    elif isinstance(node, TAbstraction):
        return has_holes(node.body)
    elif isinstance(node, TApplication):
        return has_holes(node.target)
    else:
        raise Exception("Couldnt find the node", node)
