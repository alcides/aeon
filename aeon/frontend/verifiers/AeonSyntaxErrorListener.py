from antlr4 import *
from antlr4.error.ErrorListener import ErrorListener


class AeonSyntaxErrorListener(ErrorListener):
    def __init__(self):
        super(AeonSyntaxErrorListener, self).__init__()
        self.errorsList = []

    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        error = 'SyntaxError {}:{}: {}'.format(line, column, msg)
        self.errorsList.append(error)
