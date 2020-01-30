from aeon.automatic.individual import Individual
from aeon.automatic.gen_program import GenProg

def mutate(gen_program: GenProg, individual: Individual):
    # 1. Select a random node from the tree and get its type
    # 2. insert a hole with its type
    # 3. Call the synthesizer
    # 4. Replace the hole
    # 5. Call the typechecker

def regular_mutation():
    pass

def view_point_mutation():
    pass
