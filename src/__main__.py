import sys
import os

from .frontend import parse
from .typechecker import typecheck
from .annotate import typeinfer
from .codegen import generate

if __name__ == '__main__':

    debug = '-d' in sys.argv
    inferComplexity = '--infer' in sys.argv
    refined = not ('--norefine' in sys.argv)

    ast = parse(sys.argv[-1])
    if debug:
        print("Untyped ast:")
        for decl in ast:
            print("\t", decl)
        print()
    ast, context, tcontext = typecheck(ast, refined=refined)

    if debug:
        print()
        print("Typed ast:")
        for decl in ast:
            print("\t", decl)
        print()
        print()
        
    if inferComplexity:
        typeinfer(ast, context, tcontext)

    output = generate(ast, context, tcontext)

    try:
        os.mkdir('bin')
    except:
        pass
    open('bin/E.java', 'w').write(output)
