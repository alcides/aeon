import random

# Randomly selects an individual from the population
def random_selection(population):
    index = random.randint(0, len(population) - 1)
    return population[index]