from aeon.ast import Var, Hole, Literal, If, Application, Abstraction, TAbstraction, TApplication, Definition

def depth(node):
    if isinstance(node, str):
        return 1
    if isinstance(node, Var):
        return 1
    elif isinstance(node, Hole):
        return 1
    elif isinstance(node, Literal):
        return 1
    elif isinstance(node, If):
        return 1 + max(depth(node.cond), depth(node.then), depth(node.otherwise))
    elif isinstance(node, Application):
        return 1 + max(depth(node.target), depth(node.argument))
    elif isinstance(node, Abstraction):
        return 1 + depth(node.body)
    elif isinstance(node, TApplication):
        return 1 + depth(node.target)
    elif isinstance(node, TAbstraction):
        return 1 + depth(node.body)
    elif isinstance(node, Definition):
        return 1 + depth(node.body)
    else:
        raise Exception('Forgotten node in depth: ', type(node), node)
