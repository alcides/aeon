
from .frontend_module.AeonASTVisitor import AeonASTVisitor

from .frontend_module.generated.AeonParser import AeonParser
from .frontend_module.generated.AeonLexer import AeonLexer

from .frontend_module.verifiers.ContextVerifier import ContextVerifier
from .frontend_module.verifiers.AeonSyntaxErrorListener import AeonSyntaxErrorListener

import os
import sys 
import os.path

from antlr4 import *
from .ast import Import
from .ast import Program
from .ast import Definition

# Given a file, parses the file and imports the program
def parse(path):
    
    import aeon3.stdlib
    
    input_stream = FileStream(path)
    tree = parse_input(input_stream)
    
    # Build the program
    initial_context = aeon3.stdlib.initial_context
    program = AeonASTVisitor(initial_context).visit(tree)
    
    # Check if the imports are proper and resolve the imports
    if runImportVerifier(tree):
        program = resolveImports(path, program)

    # Run the verifiers to search for errors
    # runVerifiers(tree)
    
    return program
    
# Given an expression of a program, parse it and imports it
def parse_strict(text):
    input_stream = InputStream(text)
    tree = parse_input(input_stream)
    
    # Build the program and return it
    program = AeonASTVisitor({}).visit(tree)
    
    return program.declarations[0]
    
def parse_input(input_stream):

    # Initialize error listener
    syntax_error_listener = AeonSyntaxErrorListener()

    # Initialize lexer, tokens and parser
    lexer = AeonLexer(input_stream)
    tokens = CommonTokenStream(lexer)
    parser = AeonParser(tokens)

    # Add default error listener to lexer and parser
    lexer.removeErrorListeners()
    parser.removeErrorListeners()
    lexer.addErrorListener(syntax_error_listener)
    parser.addErrorListener(syntax_error_listener)
    
    tree = parser.aeon()

    # Print the errors and exit
    if syntax_error_listener.errorsList:
        [print(error) for error in syntax_error_listener.errorsList]
        sys.exit(-1)
    
    return tree

def runImportVerifier(tree):
    return True


def runVerifiers(tree):
    errorsList = []
    ContextVerifier(errorsList).visit(tree)


    # Print the errors and exit
    if errorsList:
        [print(error) for error in errorsList]
        sys.exit(-1)

    
# Resolves the imports
def resolveImports(path, program):
    result = []
    for declaration in program.declarations:
        if type(declaration) is Import:
            importPath = declaration.name + '.ae'
            joinedPath = os.path.join(os.path.dirname(path), importPath)
            realPath = os.path.realpath(joinedPath)
            importedProgram = parse(realPath)
            
            # If we only want a specific function from the program
            if declaration.function is not None:
                importedProgram.declarations = list(filter(lambda x : type(x) is Definition \
                                            and x.name == declaration.function, \
                                            importedProgram.declarations))
            result = importedProgram.declarations + result
        else:
            result.append(declaration)
    return Program(result)