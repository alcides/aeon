import random

from aeon.automatic.individual import Individual

from aeon.types import TypingContext
from aeon.ast import *
from aeon.synthesis import se, set_genetics, reset_genetics

def mutate(context: TypingContext, depth: int, individual: Individual):

    # Choose a hole to be mutated
    hole = random.choice(individual.synthesized)
    print("\nChose the hole:", hole, "\n\n")
    # Choose what parent node will have one of its son mutated, typee is son type
    parent_node, son_node = choose_node(hole, context.copy())
    print("The parent node and son nodes are\n", parent_node, "\n", son_node, "\n\n")
    # Split the remaining tree into subtrees array, filter then and set their height
    subtrees = split_trees(son_node, 0)
    print("All the subtrees are", subtrees, "\n\n") 
    subtrees = filter_trees(subtrees, context)

    # Add the genetic material to the synthesis procedure
    # Synthesize the mutation
    set_genetics(subtrees)
    mutation = se(context, son_node.type, depth)
    reset_genetics()

    print("Generated the mutation\n", mutation, "\n\n")

    # Replace the dead node
    mutate = replace_son(parent_node, mutation, son_node)

    print("The final mutant is\n", mutate, '\n\n')

    return mutate

# Returns the parent and its selected son for mutation
# TODO: super naive implementation, not all nodes have the same odd of being chosen
def choose_node(node, ctx: TypingContext):

    keep_recursion = None

    if isinstance(node, Literal) or isinstance(node, Var):
        choices = [node]
    elif isinstance(node, If):
        choices = [node, node.cond, node.then, node.otherwise, keep_recursion]
    elif isinstance(node, Application):
        choices = [node, node.target, node.argument, keep_recursion]
    elif isinstance(node, Abstraction):
        choices = [node, node.body, keep_recursion]
        ctx = ctx.add_var(node.arg_name, node.arg_type)
    elif isinstance(node, TAbstraction):
        choices = [node, node.body, keep_recursion]
    elif isinstance(node, TApplication):
        choices = [node. node.target, keep_recursion]
    
    choice = random.choice(choices)

    if not choice:
        choice = choose_node(random.choice(choices[:-1]), ctx)[1]
    
    return (node, choice)

def split_trees(node, height: int):
    
    node.height = height
    height += 1

    if isinstance(node, Literal) or isinstance(node, Var):
        return [node]

    elif isinstance(node, If):
        cond = split_trees(node.cond, height)
        then = split_trees(node.then, height)
        other = split_trees(node.otherwise, height)
        return [node] + cond + then + other
    
    elif isinstance(node, Application):
        target = split_trees(node.target, height)
        argument = split_trees(node.argument, height)
        return [node] + target + argument
    
    elif isinstance(node, Abstraction):
        return [node] + split_trees(node.body, height)
    
    elif isinstance(node, TAbstraction):
        return [node] + split_trees(node.body, height)
    
    elif isinstance(node, TApplication):
        return [node] + split_trees(node.target, height)
    
    else:
        raise Exception("Unknown node when splitting trees", e)
    
    return None # Never happens


def filter_trees(trees, context):
    def filter_tree(node: TypedNode, ctx):
        if isinstance(node, Literal):
            return True
        
        elif isinstance(node, Var):
            return node.name in context.variables
        
        elif isinstance(node, If):
            return filter_tree(node.cond, ctx) and filter_tree(node.then, ctx) and\
                                              filter_tree(node.otherwise, ctx)
        
        elif isinstance(node, Application):
            return filter_tree(node.target, ctx) and filter_tree(node.argument, ctx)
        
        elif isinstance(node, Abstraction):
            return filter_tree(node.body, ctx.with_var(node.arg_name, node.arg_type))
        
        elif isinstance(node, TAbstraction): # TODO: Falta filtrar TAbstractions
            return filter_tree(node.body, ctx)
        
        elif isinstance(node, TApplication): # TODO: Falta filtrar TApplication
            return filter_tree(node.target, ctx)
        
        else:
            raise Exception("Unknown node when filtering", e)

        return None # Never happens

    return [tree for tree in trees if filter_tree(tree, context)]
    
# Replaces the nodes' son with the mutation
def replace_son(node, mutation, son_node):
    if isinstance(node, Literal) or isinstance(node, Var):
        node = mutation

    elif isinstance(node, If):
        if node.cond.type == son_node:
            node.cond = mutation
        elif node.then.type == son_node:
            node.then = mutation
        else:
            node.otherwise = mutation
    
    elif isinstance(node, Application):
        if node.target == son_node:
            node.target = mutation
        else:
            node.argument = mutation
    
    elif isinstance(node, Abstraction) or isinstance(node, TAbstraction):
        node.body = mutation
    
    elif isinstance(node. TApplication):
        node.target = mutation
    
    else:
        raise Exception("Unknown node when replacing", e)
    
    return node