from typing import List

from aeon.automatic.individual import Individual

import random
from statistics import median

def select(population: List[Individual], size_tests: int):
    return e_lexicase_selection(population, size_tests)

def tournament_selection(population: List[Individual]):
    pass

def e_lexicase_selection(population: List[Individual], size_tests: int):
    def get_parent(population, test_cases):
        pop = population.copy()
        test_cases = test_cases.copy()

        while len(test_cases) > 0 and len(pop) > 1:
            test = random.choice(test_cases)
            elite = min(individual.fitness[test] for individual in pop)
            error = median_absolute_deviation(population, test)
            erros_all = [individual.fitness[test] for individual in population]
            
            for individual in pop:
                if individual.fitness[test] > elite + error:
                    pop.remove(individual)
            test_cases.remove(test)
        
        return random.choice(pop)

    parents = []
    test_cases = list(range(size_tests)) # Indexes of the tests    

    # used for multiple events
    # number of selections = amount of parents
    #for _ in range(round(len(parents) * 0.1)):
    #    print("Starting")
    #    result.append(get_parent(population, test_cases))

    return get_parent(population, test_cases)

# Auxiliary function
def median_absolute_deviation(population, test):
    # Obtain the test case results
    errors = [individual.fitness[test] for individual in population]
    median_errors = median(errors)
    return median([abs(et - median_errors) for et in errors])
