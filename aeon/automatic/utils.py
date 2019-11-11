from aeon.ast import Var, Abstraction, Application, TApplication, TAbstraction


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
        if not typee.arg_name.name.startswith("_"):
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


# =============================================================================
# ============================================= TEMP - GOING TO BE REMOVED SOON
def get_holes(node):
    if isinstance(node, Hole):
        return [node.type]
    elif isinstance(node, Literal):
        return []
    elif isinstance(node, Var):
        return []
    elif isinstance(node, If):
        return get_holes(node.cond) + get_holes(node.then) + get_holes(
            node.otherwise)
    elif isinstance(node, Application):
        return get_holes(node.target) + get_holes(node.argument)
    elif isinstance(node, Abstraction):
        return get_holes(node.body)
    elif isinstance(node, TAbstraction):
        return get_holes(node.body)
    elif isinstance(node, TApplication):
        return get_holes(node.target)
    else:
        return []


def replace_holes(node, holes):
    if isinstance(node, If):
        if type(node.cond) is Hole:
            node.cond = holes.pop(-1)
        else:
            replaceHoles(node.cond, holes)
        if type(node.then) is Hole:
            node.then = holes.pop(-1)
        else:
            replaceHoles(node.then, holes)
        if type(node.otherwise) is Hole:
            node.otherwise = holes.pop(-1)
    elif isinstance(node, Application):
        if type(node.target) is Hole:
            node.target = holes.pop(-1)
        else:
            replaceHoles(node.target, holes)
        if type(node.argument) is Hole:
            node.argument = holes.pop(-1)
        else:
            replaceHoles(node.argument)
    elif isinstance(node, Abstraction):
        if type(node.body) is Hole:
            node.body = holes.pop(-1)
        else:
            replaceHoles(node.body)
    elif isinstance(node, TAbstraction):
        if type(node.body) is Hole:
            node.body = holes.pop(-1)
        else:
            replaceHoles(node.body)
    elif isinstance(node, TApplication):
        if type(node.target) is Hole:
            node.target = holes.pop(-1)
        else:
            replaceHoles(node.body)
    else:
        raise Exception("Trying to replace unknown node: ", type(node), node)
