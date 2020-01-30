from functools import total_ordering

# Represents an individual with fitness
@total_ordering
class Individual(object):
    def __init__(self, synthesized=None):
        self.fitness = None
        self.synthesized = synthesized
    
    def with_fitness(self, fitness):
        self.fitness = fitness

    def with_synthesized(self, synth):
        self.synthesized = synth

    # Default functions
    def _is_valid_operand(self, other):
        return (hasattr(other, "ast") and
                hasattr(other, "fitness"))

    def __eq__(self, other):
        if not self._is_valid_operand(other):
            raise Exception("Operand is invalid", other)
        return self.ast == other.ast
    
    # TODO: Check if this is valid, or if I may have problems because of eq
    def __lt__(self, other):
        if not self._is_valid_operand(other):
            raise Exception("Operand is invalid", other)
        return self.fitness < other.fitness
    
    def __repr__(self):
        return str(self)

    def __str__(self):
        return "{}\t:\t{}".format(self.fitness, self.ast)
