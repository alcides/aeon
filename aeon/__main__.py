import sys
import os
import random
import shutil


from .frontend import parse
from .automatic import synthesise_with_outputdir 
from .typechecker import typecheck
from .annotate import typeinfer
from .codegen import generate

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
    if debug:
        print("Untyped ast:")
        for decl in ast:
            print("\t", decl)
        print()
    

    ast, context, tcontext = typecheck(ast, refined=refined, synthesiser=synthesise_with_outputdir(outputdir))

    if debug:
        print()
        print("Typed ast:")
        for decl in ast:
            print("\t", decl)
        print()
        print()
        
    if inferComplexity:
        typeinfer(ast, context, tcontext)

    output = generate(ast, context, tcontext, class_name='E', generate_file=True, outputdir=outputdir)