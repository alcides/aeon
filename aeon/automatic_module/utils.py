def get_holes(node):
    if type(node) is Hole:
        return [node.type]
    elif type(node) is Literal:
        return []
    elif type(node) is Var:
        return []
    elif type(node) is If:
        return get_holes(node.cond) + get_holes(node.then) + get_holes(
            node.otherwise)
    elif type(node) is Application:
        return get_holes(node.target) + get_holes(node.argument)
    elif type(node) is Abstraction:
        return get_holes(node.body)
    elif type(node) is TAbstraction:
        return get_holes(node.body)
    elif type(node) is TApplication:
        return get_holes(node.target)
    else:
        return []


def replaceHoles(node, holes):
    if type(node) is If:
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
    elif type(node) is Application:
        if type(node.target) is Hole:
            node.target = holes.pop(-1)
        else:
            replaceHoles(node.target, holes)
        if type(node.argument) is Hole:
            node.argument = holes.pop(-1)
        else:
            replaceHoles(node.argument)
    elif type(node) is Abstraction:
        if type(node.body) is Hole:
            node.body = holes.pop(-1)
        else:
            replaceHoles(node.body)
    elif type(node) is TAbstraction:
        if type(node.body) is Hole:
            node.body = holes.pop(-1)
        else:
            replaceHoles(node.body)
    elif type(node) is TApplication:
        if type(node.target) is Hole:
            node.target = holes.pop(-1)
        else:
            replaceHoles(node.body)
    else:
        raise Exception("Trying to replace unknown node: ", type(node), node)
