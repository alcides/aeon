from aeon.ast import Var, Hole, Literal, If, Application, Abstraction, TAbstraction, TApplication, Definition

def count_nodes(node):
    if isinstance(node, str):
        return 1
    if isinstance(node, Var):
        return 1
    elif isinstance(node, Hole):
        return 1
    elif isinstance(node, Literal):
        return 1
    elif isinstance(node, If):
        return 1 + count_nodes(node.cond) + count_nodes(node.then) + count_nodes(node.otherwise)
    elif isinstance(node, Application):
        return 1 + count_nodes(node.target) + count_nodes(node.argument)
    elif isinstance(node, Abstraction):
        return 1 + count_nodes(node.body)
    elif isinstance(node, TApplication):
        return 1 + count_nodes(node.target)
    elif isinstance(node, TAbstraction):
        return 1 + count_nodes(node.body)
    elif isinstance(node, Definition):
        return 1 + count_nodes(node.body)
    else:
        raise Exception('Forgotten node in count_nodes: ', type(node), node)