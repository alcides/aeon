import sys
import os
import random
import shutil

from .frontend import parse
from .frontend import parse_strict
from .typechecker import check_program
from .type_inferer import inferTypes
from .interpreter import run

from .translate import Translator

sys.setrecursionlimit(sys.getrecursionlimit() * 5)

if __name__ == '__main__':
    debug = '-d' in sys.argv
    should_print_fitness = '--fitness' in sys.argv
    seed = 0
    for arg in sys.argv:
        if arg.startswith("--seed="):
            seed = int(arg[7:])

    random.seed(seed)

    ast = parse(sys.argv[-1])
    if debug:
        print(20 * "-", "Aeon to AeonCore transformation:")
        print(ast)

    inferTypes(ast)
    if debug:
        print(20 * "-", "Type inference:")
        print(ast)

    #print(Translator().translate(ast))
    if debug:
        print(20 * "-", "Prettify:")
        print(ast)

    print(20 * "-", "First 10 random individuals:")

    try:
        ast = check_program(ast)
    except Exception as t:
        raise t
        sys.exit(-1)

    if debug:
        print("----------- Typed --------")
        print(ast)
        print("--------------------------")

    run(ast)
