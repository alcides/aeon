from aeon.synthesis import se
from aeon.evaluation.measurer import Measurer
from aeon.types import TypingContext, BasicType
from aeon.interpreter import run


def generate_and_benchmark(typee, pretty_typee, depth, pop_size, file_writer,
                           wrapper):
    population = list()
    eval_results = list()
    i = 0
    j = 0
    while i < pop_size and j < 3 * pop_size:
        j += 1
        try:
            ctx = TypingContext()
            ctx.setup()
            expression = se(ctx, typee, depth)
            print('Generated individual:', expression)
            population.append(expression)
            p = wrapper(expression)
            r = run(p)
            eval_results.append(r)
            i += 1
        except Exception as e:
            print("Not able to synthesise:", e)
    measurer = Measurer(file_writer)
    measurer.measure(typee, pretty_typee, population, eval_results)
