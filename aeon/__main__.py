import sys
import os
import random
import shutil

from .frontend import parse, parse_strict
from .frontend2 import parse as parse2
from .typechecker import check_program
from .hole_inferer import infer_hole
from .interpreter import run
from .automatic import automatic
from .translate import Translator

sys.setrecursionlimit(sys.getrecursionlimit() * 5)

if __name__ == '__main__':

    debug = '-d' in sys.argv
    should_print_fitness = '--fitness' in sys.argv
    for arg in sys.argv:
        if arg.startswith("--seed="):
            seed = int(arg[7:])
            random.seed(seed)
    fname = sys.argv[-1]

    if fname.endswith(".ae2"):
        ast = parse2(fname)
    else:
        ast = parse(fname)
    if debug:
        print(20 * "-", "Aeon to AeonCore transformation:")
        print(ast)

    if debug:
        print(20 * "-", "Prettify:")
        print(ast)

    try:
        # Infer the holes
        # infer_hole(ast)
        ast, context, holed = check_program(ast)

        # If there are holes, lets fill them
        if holed:
            ast = automatic(ast, context, holed)

    except Exception as t:
        raise t
        sys.exit(-1)

    if debug:
        print("----------- Typed --------")
        print(ast)
        print("--------------------------")

    run(ast)
