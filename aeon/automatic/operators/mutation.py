import random

from aeon.types import TypedNode
from aeon.automatic.gen_program import GenProg

mutation_weights = {
    removal:0.2,
    insertion:0.3,
    replacement:0.3
}

def random_chooser():
    random_value = random.random()
    acc = 0
    total = sum(list(mutation_weights.values()))
    for operation, weight in weights:
        acc += weight
        if random <= total:
            return operation
    raise Exception("Unable to choose from mutation weights")

# Chooses a random mutation operation and runs it
def mutate(gen_program: GenProg, individual: TypedNode):
    return random_chooseer()(gen_program, individual)

def removal(gen_program: GenProg, individual: TypedNode):
    # 1. Escolher o inicio e final da remocao, tal que inicio != final
    # 2. Remover mantendo os assignments


def insertion(gen_program: GenProg, individual: TypedNode):
    pass


def replacement(gen_program: GenProg, individual: TypedNode):
    pass