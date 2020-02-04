from aeon.synthesis import se_safe
from aeon.automatic.individual import Individual

def initialize(holes, size: int, depth: int):
    # Chose the ramped half half implementation
    return ramped_half_half(holes, size, depth)

def grow(holes, size: int, depth: int):
    population = []

    for i in range(size):
        expressions = [se_safe(ctx, hole, depth) for ctx, hole in holes]
        contexts = [ctx for ctx, hole in holes]    
        population.append(Individual(expressions, contexts))
        print(expressions)
    
    return population

# size > depth
def full(holes, size: int, depth: int):
    population = []
    size_per_depth = size // depth

    for i in range(depth):
        for j in range(size_per_depth):
            expressions = [se_safe(ctx, hole, i) for ctx, hole in holes]
            contexts = [ctx for ctx, hole in holes]
            print(expressions)
            population.append(Individual(expressions, contexts))
    
    for i in range(size % depth):
        expressions = [se_safe(ctx, hole, depth) for ctx, hole in holes]
        contexts = [ctx for ctx, hole in holes]
        print(expressions)
        population.append(Individual(expressions, contexts))

    return population

def ramped_half_half(holes, size: int, depth: int):
    pop_full = full(holes, size // 2 + size % 2, depth)
    pop_grow = grow(holes, size // 2, depth)

    return pop_full + pop_grow