from .AeonASTVisitor import AeonASTVisitor

from .generated.AeonParser import AeonParser
from .generated.AeonLexer import AeonLexer

from aeon.libraries.helper import importNative

# from .frontend_module.verifiers.ContextVerifier import ContextVerifier
from .verifiers.AeonSyntaxErrorListener import AeonSyntaxErrorListener

import os
import sys
import os.path

from antlr4 import *
from aeon.ast import Var, Import, Definition, Program

# Given a file, parses the file and imports the program
def parse(path):

    from aeon.libraries.stdlib import initial_context

    input_stream = FileStream(path)
    tree = parse_input(input_stream)

    # Build the program
    context = initial_context
    aeonVisitor = AeonASTVisitor(context)
    program = aeonVisitor.visit(tree)

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

    return program


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
    from ..libraries.stdlib import add_function
    for node in program.declarations:
        if isinstance(node, Import):
            # Get the os path for the ae file

            importPath = node.name
            absolutePath = os.path.normpath(
                os.path.join(os.getcwd(), os.path.dirname(path), importPath))
            realPath = absolutePath + ".ae"

            # It is a regular .ae import
            if os.path.exists(realPath):
                importedProgram = parse(realPath)
                # If we only want a specific function from the program
                if node.function is not None:
                    importedProgram.declarations = list(filter(lambda x : isinstance(x, Definition) \
                                                and x.name == node.function, \
                                                importedProgram.declarations))
            # It is a .py import
            else:
                moduleName = node.name.replace("/", ".")
                importedProgram = Program([])
                natives = importNative(
                    moduleName,
                    '*' if node.function is None else node.function)
                for native in natives.keys():
                    aetype_code, function = natives[native]

                    imported_declarations = parse_strict(
                        aetype_code).declarations
                    aetype = imported_declarations[0]  # Fixed
                    if isinstance(aetype, Definition):
                        add_function(aetype.name, aetype.type, function)
                    importedProgram.declarations.append(aetype)
                    importedProgram.declarations.extend(
                        imported_declarations[1:])
            result = result + importedProgram.declarations
        else:
            result.append(node)
    return Program(result)
