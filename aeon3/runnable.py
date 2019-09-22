from frontend_module.AeonASTVisitor import AeonASTVisitor

from frontend_module.generated.AeonParser import AeonParser
from frontend_module.generated.AeonLexer import AeonLexer

from ast import *
from antlr4 import *
from types4 import *

from frontend import *

def printAST(node):

    print(type(node), node)

    if type(node) == Program:
        for decl in node.declarations:
            print(30 * '=')
            printAST(decl)

    elif type(node) == Hole:
        printAST(node.type)

    elif type(node) == Literal:
        print(node.value, type(node.value))
        printAST(node.type)

    elif type(node) == Var:
        print(node.name, node.type)

    elif type(node) == If:
        printAST(node.cond)
        printAST(node.then)
        printAST(node.otherwise)

    elif type(node) == Application:
        printAST(node.target)
        printAST(node.argument)

    elif type(node) == Abstraction:
        printAST(node.arg_name)
        printAST(node.arg_type)
        printAST(node.body)

    elif type(node) == TAbstraction:
        printAST(node.typevar)
        printAST(node.kind)
        printAST(node.body)

    elif type(node) == TApplication:
        printAST(node.target)
        printAST(node.argument)

    elif type(node) == Definition:
        printAST(node.name)
        printAST(node.type)
        printAST(node.body)

    elif type(node) == TypeAlias:
        printAST(node.name)
        printAST(node.type)

    elif type(node) == TypeDeclaration:
        printAST(node.name)
        printAST(node.kind)

    elif type(node) == Import:
        printAST(node.name)
        if node.function is not None:
            printAST(node.function)

    elif type(node) == BasicType:
        print(node.name)

    elif type(node) == AbstractionType:
        print(node.name)
        printAST(node.arg_type)
        printAST(node.return_type)

    elif type(node) == RefinedType:
        print(node.name, type(node.name))
        printAST(node.type)
        printAST(node.cond)
    
    elif type(node) == TypeAbstraction:
        printAST(node.name)
        printAST(node.kind)

    elif type(node) == TypeApplication:
        printAST(node.target)
        printAST(node.argument)

    elif type(node) == Kind:
        print(node)

    elif type(node) == str:
        print(node)

    else:
        print("Type of node not found: ", type(node), node)

printAST(parse(sys.argv[1]))