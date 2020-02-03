from aeon.synthesis import se
from aeon.automatic.individual import Individual

def initialize(holes, size: int, depth: int):
    # Chose the ramped half half implementation
    return grow(holes, size, depth)

def grow(holes, size: int, depth: int):
    population = []

    for i in range(size):
        expressions = [se(ctx, hole, depth) for ctx, hole in holes]
        population.append(Individual(expressions))
        print("Generated", expressions)
    
    return population

# size > depth
def full(holes, size: int, depth: int):
    population = []
    size_per_depth = size // depth

    for i in range(depth):
        for j in range(size_per_depth):
            expressions = [se(ctx, hole, i) for ctx, hole in holes]
            population.append(Individual(expressions))
    
    for i in range(size % depth):
        expressions = [se(ctx, hole, depth) for ctx, hole in holes]
        population.append(Individual(expressions))

    return population

def ramped_half_half(holes, size: int, depth: int):
    pop_grow = grow(holes, size // 2, depth)
    pop_full = full(holes, size // 2 + size % 2, depth)

    return pop_grow + pop_full