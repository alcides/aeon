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


def replaceHoles(node, holes):
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
