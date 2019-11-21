from .metrics.depth import depth
from .metrics.distance import compare_trees
from .metrics.node_counter import count_nodes

from aeon.automatic import generate_fitness_function
from aeon.translate import Translator


class Measurer(object):
    def __init__(self, writer):
        self.writer = writer

    def write(self, text, separator=','):
        self.writer.write(str(text))
        self.writer.write(separator)
        self.writer.flush()

    # Given a population and supposed typee to be synthesised, measure the outcomes
    def measure(self, typee, population, eval_results):
        self.write('Typee')
        self.write('Individual')
        self.write('Tree Size')
        self.write('Tree Depth')
        self.write('Diversity', '')
        #self.write('Fitness', '')
        self.write('\r\n', '')

        for individual, res in zip(population, eval_results):
            print('Evaluating:', individual)
            self.write(typee)
            self.write(individual)
            self.write(count_nodes(individual))
            self.write(depth(individual))
            self.write(res)
            self.write(
                round(
                    sum([
                        compare_trees(individual, ast2) for ast2 in population
                        if ast2 != individual
                    ]), 3), '')
            # self.write(evaluate_fitness(individual))
            self.write('\r\n', '')
