from .typestructure import *

def synthesise(hole, goal_type, function_name, function_type):
    print("looking for source code that satisfies type", goal_type)
    print("within the context of function", function_name)
    print("with type", function_type)
    return Node('literal', nodes=['1'], type=goal_type)