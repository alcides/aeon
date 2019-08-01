from AeonParser import AeonParser
from AeonLexer import AeonLexer
from AeonASTVisitor import AeonASTVisitor

from antlr4 import *

text = open("test.ae", 'r')
input_stream = FileStream("test.ae")
lexer = AeonLexer(input_stream)
tokens = CommonTokenStream(lexer)
parser = AeonParser(tokens)
tree = parser.aeon()
visitor = AeonASTVisitor()
res = visitor.visit(tree)
print(res)
