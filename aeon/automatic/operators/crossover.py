from aeon.types import TypingContext

import random
import copy 

from aeon.automatic.individual import Individual

from aeon.types import TypingContext
from aeon.ast import *
from aeon.synthesis import se_safe, set_genetics, reset_genetics

def crossover(depth: int, parent1: Individual, parent2: Individual):

    # Choose a hole to be crossoved
    chosen1 = random.choice(range(len(parent1.synthesized)))
    hole1 = parent1.synthesized[chosen1]
    
    chosen2 = random.choice(range(len(parent2.synthesized)))
    hole2 = parent2.synthesized[chosen2]
    
    # Annotate the tree with height and size useful for prob. control
    calculate_height_depth(hole1, 0)
    calculate_height_depth(hole2, 0)

    # Choose what parent node will have one of its son mutated, typee is son type
    context1 = parent1.contexts[chosen1].copy()
    parent_node1, son_node1 = choose_node(hole1, context1)

    context2 = parent2.contexts[chosen2].copy()
    parent_node2, son_node2 = choose_node(hole2, context2)

    # Split the remaining tree from parent2 into subtrees array and filter them
    subtrees2 = split_trees(son_node2)
    subtrees2 = filter_trees(subtrees2, context1) # This context is intended

    # Add the genetic material to the synthesis procedure
    # Synthesize the mutation
    set_genetics(subtrees2)
    cross = se_safe(context1, son_node1.type, depth)
    reset_genetics()

    # Replace the previous code. Careful: This changes the tree
    offspring = replace_son(parent_node1, cross, son_node1)

    new_synthesized = copy.deepcopy(parent1.synthesized)
    new_synthesized[chosen1] = offspring

    new_contexts = copy.deepcopy(parent1.contexts)

    return Individual(new_synthesized, new_contexts)

def calculate_height_depth(node: TypedNode, height: int):
    node.height = height

    if isinstance(node, Literal) or isinstance(node, Var):
        node.size = 1
    
    elif isinstance(node, If):
        cond = calculate_height_depth(node.cond, height + 1)
        then = calculate_height_depth(node.then, height + 1)
        otherwise = calculate_height_depth(node.otherwise, height + 1)
        node.size = cond + then + otherwise + 1
    
    elif isinstance(node, Application):
        target = calculate_height_depth(node.target, height + 1)
        argument = calculate_height_depth(node.argument, height + 1)
        node.size = target + argument + 1
    
    elif isinstance(node, Abstraction) or isinstance(node, TAbstraction):
        body = calculate_height_depth(node.body, height + 1)
        node.size = body + 1
    
    elif isinstance(node, TApplication):
        target = calculate_height_depth(node.target, height + 1)
        node.size = target + 1
    
    else:
        raise Exception("Unkown node when calculating height and size", node)

    return node.size

def choose_node(node, ctx: TypingContext):
    
    if isinstance(node, Literal) or isinstance(node, Var):
        choices = [node]
    
    elif isinstance(node, If):
        cond = node.cond
        then = node.then
        other = node.otherwise
        choices = [node] + [cond] * cond.size + [then] * then.size +\
                                                [other] * other.size
    elif isinstance(node, Application):
        target = node.target
        argument = node.argument
        choices = [node] + [target] * target.size + [argument] * argument.size

    elif isinstance(node, Abstraction):
        body = node.body
        choices = [node] + [body] * body.size
        ctx.add_var(node.arg_name, node.arg_type)

    elif isinstance(node, TAbstraction):
        body = node.body
        choices = [node] + [body] * body.size
    
    elif isinstance(node, TApplication):
        target = node.target
        choices = [node] + [target] * node.target
    
    else:
        raise Exception("Unknown node when choosing", node)

    choice = random.choice(choices)

    if choice != node:
        choice = choose_node(choice, ctx)[1]
    
    return node, choice

def split_trees(node):

    if isinstance(node, Literal) or isinstance(node, Var):
        return [node]

    elif isinstance(node, If):
        cond = split_trees(node.cond)
        then = split_trees(node.then)
        other = split_trees(node.otherwise)
        return [node] + cond + then + other
    
    elif isinstance(node, Application):
        target = split_trees(node.target)
        argument = split_trees(node.argument)
        return [node] + target + argument
    
    elif isinstance(node, Abstraction):
        return [node] + split_trees(node.body)
    
    elif isinstance(node, TAbstraction):
        return [node] + split_trees(node.body)
    
    elif isinstance(node, TApplication):
        return [node] + split_trees(node.target)
    
    else:
        raise Exception("Unknown node when splitting trees", node)
    
    return None # Never happens


def filter_trees(trees, context):
    def filter_tree(node: TypedNode, ctx):
        if isinstance(node, Literal):
            return True
        
        elif isinstance(node, Var):
            return node.name in ctx.variables
        
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
            raise Exception("Unknown node when filtering", node)

        return None # Never happens

    return [tree for tree in trees if filter_tree(tree, context)]
    
# Replaces the nodes' son with the mutation
def replace_son(node, mutation, son_node):

    if node == son_node:
        node = mutation

    elif isinstance(node, Literal) or isinstance(node, Var):
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
    
    elif isinstance(node, TApplication):
        node.target = mutation
    
    else:
        raise Exception("Unknown node when replacing", node)
    
    return node