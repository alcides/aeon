from aeon.synthesis import se_safe
from aeon.automatic.individual import Individual

from aeon.automatic.utils.tree_utils import annotate_tree

# =============================================================================
# Grow strategy: individuals may or may not have the forced depth
def grow(holes, size, depth):

    population = []

    for i in range(size):
        synthesized = [se_safe(ctx, hole, depth) for ctx, hole in holes]
        # Annotate the expressions with its height, depth and size
        any(annotate_tree(x) for x in synthesized)
        contexts = [ctx for ctx, hole in holes]
        population.append(Individual(contexts, synthesized))
    
    return population
