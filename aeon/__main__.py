import sys
import os
import random
import shutil

from .frontend import parse
from .typechecker import typecheck, TypeException
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
