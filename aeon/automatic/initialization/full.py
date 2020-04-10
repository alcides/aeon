from aeon.synthesis import se_safe
from aeon.automatic.individual import Individual

from aeon.automatic.utils.tree_utils import annotate_tree

# =============================================================================
# Full strategy: individuals full depth is partitioned between the population
def full(holes, size, depth):
    
    population = []
    size_per_depth = size // depth

    # Generate a certain amount of population with that max depth
    for i in range(depth):
        for _ in range(size_per_depth):
            expressions = [se_safe(ctx, hole, i) for ctx, hole in holes]
            # Annotate the expressions with its height, depth and size
            any(annotate_tree(x) for x in expressions)
            contexts = [ctx for ctx, hole in holes]
            population.append(Individual(contexts, expressions))
    
    # The remaining population has the maximum depth
    for _ in range(size % depth):
        expressions = [se_safe(ctx, hole, depth) for ctx, hole in holes]
        # Annotate the expressions with its height, depth and size
        any(annotate_tree(x) for x in expressions)
        contexts = [ctx for ctx, hole in holes]
        population.append(Individual(contexts, expressions))

    return population


