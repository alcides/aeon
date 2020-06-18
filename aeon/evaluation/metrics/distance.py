from aeon.ast import Var, Hole, Literal, If, Application, Abstraction, TAbstraction, TApplication

import zss
import Levenshtein


# Used for the tree edit distance
class DistanceNode(object):
    @staticmethod
    def get_children(node):
        if isinstance(node, str):
            return list()
        if isinstance(node, Hole):
            return list()
        if isinstance(node, Var):
            return list()
        if isinstance(node, Literal):
            return list()
        if isinstance(node, If):
            return [node.cond, node.then, node.otherwise]
        if isinstance(node, Application):
            return [node.target, node.argument]
        if isinstance(node, Abstraction):
            return [node.body]
        if isinstance(node, TAbstraction):
            return [node.body]
        if isinstance(node, TApplication):
            return [node.target]
        else:
            raise Exception("Forgot the node: ", type(node), node)

    @staticmethod
    def get_label(node):
        return node

    @staticmethod
    def distance(node1, node2):

        if node1 is '' or node2 is '':
            return 1

        if type(node1) != type(node2):
            return 1

        if isinstance(node1, Literal) and isinstance(node2, Literal):
            value1 = node1.value
            value2 = node2.value

            if isinstance(value1, str):
                if isinstance(value2, str):
                    return (1 -
                            pow(0.99, Levenshtein.distance(value1, value2)))
                else:
                    return 1
            elif isinstance(value2, str):
                return 1
            else:
                if isinstance(value1, bool):
                    if isinstance(value2, bool):
                        return abs(value1 - value2)
                    else:
                        return 1
                # value1 is not boolean and value 2 is boolean
                if isinstance(value2, bool):
                    return 1

                result = 1 if type(value1) != type(value2) else 0
                return result + (1 - pow(0.99, abs(value1 - value2)))

        if isinstance(node1, Var) and isinstance(node2, Var):
            return 1 if node1.name != node2.name else 0

        return 0


def compare_trees(ast1, ast2):
    return zss.simple_distance(ast1, ast2, DistanceNode.get_children,
                               DistanceNode.get_label, DistanceNode.distance)
