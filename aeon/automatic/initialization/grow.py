from aeon.synthesis import se_safe
from aeon.automatic.individual import Individual

# =============================================================================
# Grow strategy: individuals may or may not have the forced depth
def grow(holes, size, depth):

    population = []

    for i in range(size):
        synthesized = [se_safe(ctx, hole, depth) for ctx, hole in holes]
        contexts = [ctx for ctx, hole in holes]
        population.append(Individual(contexts, synthesized))
    
    return population
