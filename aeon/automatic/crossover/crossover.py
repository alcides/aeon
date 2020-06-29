import copy
import random

from aeon.typechecker.subtyping import is_subtype
from aeon.synthesis.synthesis import se_safe, set_genetics, reset_genetics

from aeon.automatic.individual import Individual
from aeon.automatic.utils.utils import treattype
from aeon.automatic.utils.tree_utils import annotate_tree, random_subtree, replace_tree, all_valid_subtrees

# Chooses a specific hole whose tree is going to be crossed with
def regular_crossover(depth, parent1, parent2, hole_types):
    
    # Choose the index of the hole to be crossed
    index_hole = random.choice(range(len(parent1.synthesized)))

    # Obtain the holes and contexts from each parent
    hole1 = parent1.synthesized[index_hole].copy()
    context1 = parent1.contexts[index_hole].copy()

    hole2 = parent2.synthesized[index_hole].copy()
    context2 = parent2.contexts[index_hole].copy()

    # Choose the subtree that is getting replaced
    father1, subtree1 = random_subtree(hole1)

    # Obtain all valid subtrees from the second parent
    subtrees2 = all_valid_subtrees(context2, hole2)

    # Filter for those that respect the maximum depth and type of subtree1
    T = treattype(hole_types[index_hole], father1, subtree1)
    subtrees2 = list(filter(lambda x: x.depth <= depth - subtree1.height, subtrees2))
    subtree_selections = list(filter(lambda x: is_subtype(context1, x.type, T), subtrees2))
    
    if not subtree_selections:
        # If no valid subtree is available to cross, synthesize an expression
        set_genetics(subtrees2)
        
        # TODO: atualizar o context1

        subtree2 = se_safe(context1, subtree1.type, depth - subtree1.height)
        reset_genetics()
    else:
        subtree2 = random.choice(subtree_selections)
    
    # Create the offspring by crossing the two trees
    offspring = replace_tree(hole1, father1, subtree1, subtree2) 

    # Update the offspring height, depth and size
    annotate_tree(offspring)

    # Obtain a copy of the Individual contents
    contexts = [ctx.copy() for ctx in parent1.contexts]
    synthesized = [expr.copy() for expr in parent1.synthesized]
    synthesized[index_hole] = offspring

    return Individual(contexts, synthesized)
