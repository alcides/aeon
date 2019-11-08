import sys
import os
import random
import shutil

from .frontend import parse
from .typechecker import typecheck, TypeException
from .typeInferer import inferTypes
from .interpreter import run

from .translate import Translator

from .automatic_module.conversor import retrieve_fitness_functions
from .automatic_module.utils import get_holes
from .automatic_module.random import Random

sys.setrecursionlimit(sys.getrecursionlimit() * 5)

if __name__ == '__main__':
    debug = '-d' in sys.argv
    seed = 0
    for arg in sys.argv:
        if arg.startswith("--seed="):
            seed = int(arg[7:])

    random.seed(seed)

    print(
        "---------------------------------------------------------\nAeonCore transformation:\n"
    )
    ast = parse(sys.argv[-1])
    print(ast)

    print(
        "---------------------------------------------------------\nType discovery:\n"
    )
    inferTypes(ast)
    print(ast)

    print(
        "---------------------------------------------------------\nAeonPretty transformation:\n"
    )
    #print(Translator().translate(ast))

    print(
        "\n-------------------------------------------------------\nFitness function generation:"
    )
    res = retrieve_fitness_functions(ast)
    if res:
        print(res)
    print("\n")

    print(
        "\n-------------------------------------------------------\nFirst 10 random individuals:"
    )
    # Temp
    '''
    for declaration in ast:
        if type(declaration) is Definition and declaration.name in res:
            holes = get_holes(declaration)
            from .libraries.stdlib import initial_context
            ctx = {}
            for name in initial_context.keys():
                ctx[name] = initial_context[name][0]
            random = Random(ctx, declaration, holes)
    '''

    if debug:
        print("---------- Untyped -------")
        print(ast)
        print("--------------------------")
    try:
        ast, context, tcontext = typecheck(ast)

    except TypeException as t:
        print(t.args[0])
        print(t.args[1])
        print("Given:")
        print(t.given)
        print("Expected:")
        print(t.expected)
        raise t
        sys.exit(-1)

    if debug:
        print("----------- Typed --------")
        print(ast)
        print("--------------------------")

    run(ast)
