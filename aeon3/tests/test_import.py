import unittest
from antlr4 import *
import sys

sys.path.append('..')

from ast import *
from types import * 

from AeonParser import AeonParser
from AeonLexer import AeonLexer
from AeonASTVisitor import AeonASTVisitor

class TestImports(unittest.TestCase):

    def assert_regularImport(self):
        importStr = 'import String'
        expects =  Import(Var('String'))
        result = parse(importStr)
        print(result, expects)
        self.assertEqual(expects, result)


def parse(text):
    lexer = AeonLexer(text)
    tokens = CommonTokenStream(lexer)
    parser = AeonParser(tokens)
    tree = parser.aeon()
    visitor = AeonASTVisitor()
    return visitor.visit(tree)

if __name__ == '__main__':
    unittest.main()
