import sys
import os
import random
import shutil

from .frontend import parse
from .automatic import synthesise_with_outputdir
from .typechecker import typecheck, TypeException
from .interpreter import run

sys.setrecursionlimit(sys.getrecursionlimit() * 5)

if __name__ == '__main__':
    debug = '-d' in sys.argv
    inferComplexity = '--infer' in sys.argv
    refined = not ('--norefine' in sys.argv)

    seed = 0
    outputdir = 'bin'
    for arg in sys.argv:
        if arg.startswith("--seed="):
            seed = int(arg[7:])
        if arg.startswith("--outputdir="):
            outputdir = arg[12:]

    random.seed(seed)

    ast = parse(sys.argv[-1])
    '''
    if debug:
        print("---------- Untyped -------")
        print(ast)
        print("--------------------------")
    try:
        ast, context, tcontext = typecheck(
            ast,
            refined=refined,
            synthesiser=synthesise_with_outputdir(outputdir))

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
    '''

    run(ast)
