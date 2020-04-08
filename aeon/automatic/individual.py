from functools import total_ordering

# Represents an individual with fitness
class Individual(object):
    def __init__(self, contexts = list(), synthesized = list()):
        self.fitness = list()
        self.contexts = contexts
        self.synthesized = synthesized
    
    # Add to the lists
    def add_fitness(self, fitness):
        self.fitness.append(fitness)

    def add_contexts(self, context):
        self.contexts.append(context)

    def add_synthesized(self, synth):
        self.synthesized.append(synth)

    # Set the lists
    def set_fitness(self, fitness):
        self.fitness = fitness

    def set_contexts(self, contexts):
        self.contexts = contexts

    def set_synthesized(self, synthesized):
        self.synthesized = synthesized

    # String representation
    def __repr__(self):
        return str(self)

    def __str__(self):
        return "Fitness: {}\r\nSynthesized expressions: {}".format(self.fitness, self.synthesized)
