import random 
import statistics

# Randomly chooses objectives and and returns a random individual that complies
def e_lexicase(population):
    def select(population, test_cases):

        pop = population.copy()
        test_cases = test_cases.copy()
        
        while len(test_cases) > 0 and len(pop) > 1:

            # Randomly chooses one of the objectives
            test = random.choice(test_cases)
            
            elite = min(individual.fitness[test] for individual in pop)
            error = median_absolute_deviation(population, test)
            
            # Filter the individuals whose fitness on the test is to high
            pop = list(filter(lambda x: x.fitness[test] <= elite + error, pop))

            # Remove the current test
            test_cases.remove(test)
        
        return random.choice(pop)

    test_cases = list(range(len(population[0].fitness)))

    return select(population, test_cases)


# Auxiliary function
def median_absolute_deviation(population, test):
    
    # Obtain the test case results
    errors = [individual.fitness[test] for individual in population]
    median_errors = statistics.median(errors)

    return statistics.median([abs(et - median_errors) for et in errors])
