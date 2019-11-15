from aeon.synthesis import se
from aeon.evaluation import Measurer
from aeon.types import TypingContext, BasicType

MAX_TREE_DEPTH = 2
POPULATION_SIZE = 100

def generate_and_benchmark(typee, file_writer):
    population = list()
    for i in range(POPULATION_SIZE):
        try:    
            ctx = TypingContext()
            ctx.setup()
            result = se(ctx, typee, MAX_TREE_DEPTH)
            print('Generated individual:', result)
            population.append(result)
        except Exception as e: 
            print("Not able to synthesise:", e)
    measurer = Measurer(file_writer)
    measurer.measure(typee, population)
