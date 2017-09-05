import sys
import os

from .frontend import parse
from .typechecker import typecheck
from .codegen import generate

if __name__ == '__main__':

    debug = len(sys.argv) > 1 and '-d' == sys.argv[1]

    ast = parse(sys.argv[-1])
    if debug:
        print("Untyped ast:")
        for decl in ast:
            print("\t", decl)
        print()
    ast, table, tcontext = typecheck(ast)

    if debug:
        print()
        print("Typed ast:")
        for decl in ast:
            print("\t", decl)
        print()
        print()
        print("Table:")
        for top in table:
            print("\t", top, "\t", table[top])
        print()

    output = generate(ast, table, tcontext)

    try:
        os.mkdir('bin')
    except:
        pass
    open('bin/E.java', 'w').write(output)
