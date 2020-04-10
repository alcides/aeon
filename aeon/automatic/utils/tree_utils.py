import random 

from aeon.ast import Hole, Var, Literal, If, Application, Abstraction, TApplication, TAbstraction, Definition

# =============================================================================
# Given a tree, annotate it with its maximum depth, size and height
def annotate_tree(tree, height = 0):
 
    tree.height = height

    if isinstance(tree, Literal) or isinstance(tree, Var) or isinstance(tree, Hole):
        tree.size = 1
        tree.depth = 1
    
    elif isinstance(tree, If):
        cond = annotate_tree(tree.cond, height + 1)
        then = annotate_tree(tree.then, height + 1)
        otherwise = annotate_tree(tree.otherwise, height + 1)

        # Update the information
        tree.size = 1 + cond + then + otherwise
        tree.depth = 1 + max(tree.cond.depth, tree.then.depth, tree.otherwise.depth)

    elif isinstance(tree, Application):
        target = annotate_tree(tree.target, height + 1)
        argument = annotate_tree(tree.argument, height + 1)
        
        # Update the information
        tree.size = 1 + target + argument
        tree.depth = 1 + max(tree.target.depth, tree.argument.depth)
    
    elif isinstance(tree, Abstraction) or isinstance(tree, TAbstraction):
        body = annotate_tree(tree.body, height + 1)
        
        # Update the information
        tree.size = 1 + body
        tree.depth = 1 + tree.body.depth
    
    elif isinstance(tree, TApplication):
        target = annotate_tree(tree.target, height + 1)
        
        # Update the information
        tree.size = 1 + target
        tree.depth = 1 + tree.target.depth
    
    else:
        raise Exception("Unknown node when annotating tree:", tree)

    return tree.size


# =============================================================================
# Obtains a random subtree and its parent of the provided tree
def random_subtree(tree):

    # Use the sizes to randomly choose one of the nodes
    if isinstance(tree, Literal):
        choices = [tree]
    
    elif isinstance(tree, Var):
        choices = [tree]
    
    elif isinstance(tree, Hole):
        choices = [tree]
    
    elif isinstance(tree, If):
        choices = [tree]
        choices += [tree.cond] * tree.cond.size
        choices += [tree.then] * tree.then.size
        choices += [tree.otherwise] * tree.otherwise.size
        
    elif isinstance(tree, Application):
        choices = [tree]
        choices += [tree.target] * tree.target.size
        choices += [tree.argument] * tree.argument.size

    elif isinstance(tree, Abstraction):
        choices = [tree]
        choices += [tree.body] * tree.body.size
        
    elif isinstance(tree, TAbstraction):
        choices = [tree]
        choices += [tree.body] * tree.body.size
        
    elif isinstance(tree, TApplication):
        choices = [tree]
        choices += [tree.target] * tree.target.size

    else:
        raise Exception('Unknown tree when choosing subtree:', tree)

    # Choose the index of the chosen subtree
    index = random.choice(range(len(choices)))

    # If we choose the current tree 
    if index == 0:
        return tree, tree
        
    # If we choose one of the sons
    else:
        parent, son = random_subtree(choices[index])
        # If the tree chose itself, the tree is its parent        
        parent = tree if parent == son else parent
        return parent, son


# =============================================================================
# Obtains all valid subtrees from a given tree
def all_valid_subtrees(context, tree):

    # By default, the current subtree is valid unless a condition doesn't hold
    is_valid = True
    
    # 3 Base cases
    if isinstance(tree, Literal):
        result = list()

    elif isinstance(tree, Var):
        is_valid = tree.name in context.variables
        result = list()

    elif isinstance(tree, Hole):
        result = list()
    
    elif isinstance(tree, If):
        cond = all_valid_subtrees(context, tree.cond)
        then = all_valid_subtrees(context, tree.then)
        otherwise = all_valid_subtrees(context, tree.otherwise)
        result = cond + then + otherwise
    
    elif isinstance(tree, Application):
        target = all_valid_subtrees(context, tree.target)
        argument = all_valid_subtrees(context, tree.argument)
        result = target + argument
    
    elif isinstance(tree, Abstraction):
        new_context = context.with_var(tree.arg_name, tree.arg_type)
        result = all_valid_subtrees(new_context, tree.body)
    
    elif isinstance(tree, TAbstraction):
        new_context = context.with_type_var(tree.typevar, tree.kind)
        result = all_valid_subtrees(new_context, tree.body)
    
    elif isinstance(tree, TApplication):
        is_valid = tree.argument in context.type_variables 
        result = all_valid_subtrees(context, tree.target)
    
    else:
        raise Exception("Unknown tree when generating valid trees", tree)

    # If all the subtrees are added, then I can add myself
    if is_valid and len(result) + 1 == tree.size:
        result = result + [tree]

    return result


# =============================================================================
# Obtains a random subtree of the provided tree
def replace_tree(original, parent, old_tree, new_tree):
    
    # If we are replacing the root, return the new tree
    if parent == old_tree:
        return new_tree
    
    if isinstance(parent, Literal):
        return new_tree

    elif isinstance(parent, Var):
        return new_tree

    elif isinstance(parent, Hole):
        return new_tree
    
    elif isinstance(parent, If):
        if parent.cond == old_tree:
            parent.cond = new_tree
        
        elif parent.then == old_tree:
            parent.then = new_tree        
        
        elif parent.otherwise == old_tree:
            parent.otherwise = new_tree

    elif isinstance(parent, Application):
        if parent.target == old_tree:
            parent.target = new_tree

        elif parent.argument == old_tree:
            parent.argument = new_tree

    elif isinstance(parent, Abstraction):
        parent.body = new_tree
        
    elif isinstance(parent, TAbstraction):
        parent.body = new_tree
        
    elif isinstance(parent, TApplication):
        parent.target = new_tree
        
    else:
        raise Exception("Unknown parent tree when replacing trees", parent)

    return original

# =============================================================================
# Given a tree, replaces all its holes
def replace_holes(node, holes):
    
    if isinstance(node, Literal):
        return node
    
    elif isinstance(node, Var):
        return node
    
    elif isinstance(node, Hole):
        return holes.pop(-1)

    elif isinstance(node, If):
        node.cond = replace_holes(node.cond, holes)
        node.then = replace_holes(node.then, holes)
        node.otherwise = replace_holes(node.otherwise, holes)
    
    elif isinstance(node, Application):
        node.target = replace_holes(node.target, holes)
        node.argument = replace_holes(node.argument, holes)
    
    elif isinstance(node, Abstraction):
        node.body = replace_holes(node.body, holes)
    
    elif isinstance(node, TAbstraction):
        node.body = replace_holes(node.body, holes)
    
    elif isinstance(node, TApplication):
        node.target = replace_holes(node.target, holes)
    
    elif isinstance(node, Definition):
        node.body = replace_holes(node.body, holes)

    else:
        raise Exception("Accessing unknown node:", node)
    
    return node