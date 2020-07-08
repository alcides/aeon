import random

# A random objective is selected and sort of roulette selection is applied
def roulette(population):
    # Obtain the index of the object we are going to test
    objective = random.randint(0, len(population[0].fitness) - 1)

    # Sort the population by the random objective fitness
    sorted_population = sorted(population, key = lambda x: x.fitness[objective])

    # Apply a gaussian random selection of an individual
    index = round(abs(random.gauss(0, len(population) // 3))) % len(population)

    return sorted_population[index]
    