from .frontend_module.AeonASTVisitor import AeonASTVisitor

from .frontend_module.generated.AeonParser import AeonParser
from .frontend_module.generated.AeonLexer import AeonLexer

import os
import os.path
from antlr4 import *
from ast import Import

# Given a file, parses the file and imports the program
def parse(file):
    input_stream = FileStream(file)
    lexer = AeonLexer(input_stream)
    tokens = CommonTokenStream(lexer)
    parser = AeonParser(tokens)
    tree = parser.aeon()
    visitor = AeonASTVisitor()
    program = visitor.visit(tree)
    program = resolve_imports(program)
    return program


# Given an expression of a program, parse it and imports it
def parse_strict(text):
    lexer = AeonLexer(InputStream(text))
    tokens = CommonTokenStream(lexer)
    parser = AeonParser(tokens)
    tree = parser.aeon()
    visitor = AeonASTVisitor()
    return visitor.visit(tree).declarations[0]

# Resolves the imports
def resolve_imports(program):
    result = []

    for declaration in program.declarations:
        # TODO:
        pass

    return program