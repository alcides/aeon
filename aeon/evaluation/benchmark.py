from aeon.synthesis import se
from aeon.evaluation.measurer import Measurer
from aeon.types import TypingContext, BasicType

def generate_and_benchmark(typee, depth, pop_size, file_writer):
    population = list()
    for i in range(pop_size):
        try:    
            ctx = TypingContext()
            ctx.setup()
            result = se(ctx, typee, depth)
            print('Generated individual:', result)
            population.append(result)
        except Exception as e: 
            print("Not able to synthesise:", e)
    measurer = Measurer(file_writer)
    measurer.measure(typee, population)
