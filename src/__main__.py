import sys
import os

from .frontend import parse
from .typechecker import typecheck
from .codegen import generate

if __name__ == '__main__':

    debug = len(sys.argv) > 1 and '-d' == sys.argv[1]

    ast = parse(sys.argv[-1])
    ast, table = typecheck(ast)

    if debug:
        print("Typed ast:")
        for decl in ast:
            print("\t", decl)
        print("Table:")
        for top in table:
            print("\t", top)

    output = generate(ast, table)

    try:
        os.mkdir('bin')
    except:
        pass
    open('bin/E.java', 'w').write(output)
