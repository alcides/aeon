# type: ignore[no-redef]

from .ast import *
from .types import *

from multipledispatch import dispatch


class Translator():
    def __init__(self):
        self.tab_size = 0

    @dispatch(Program)
    def translate(self, node):
        result = ''
        for declaration in node.declarations:
            self.tab_size = 0
            translation = self.translate(declaration)
            if len(translation) > 0:
                result = '{}{}\r\n'.format(result, translation)
        return result

    @dispatch(Hole)
    def translate(self, node):
        return '[{}]'.format(
            self.translate(node.type) if node.type is not None else '')

    @dispatch(Literal)
    def translate(self, node):
        return str(node)

    @dispatch(Var)
    def translate(self, node):
        return node.name

    @dispatch(If)
    def translate(self, node):
        if is_statement(node.then) or is_statement(node.otherwise):
            self.tab_size += 1
            cond = self.translate(node.cond)
            then = self.translate(node.then)
            otherwise = self.translate(node.otherwise)
            tab = self.tab()
            self.tab_size -= 1
            return 'if {} {{\r\n{}{};\r\n{}}} else {{\r\n{}{};\r\n{}}}'.format(
                cond, tab, then, self.tab(), tab, otherwise, self.tab())
            self.tab_size -= 1
        else:
            return '{} ? {} : {}'.format(self.translate(node.cond),
                                         self.translate(node.then),
                                         self.translate(node.otherwise))

    @dispatch(Application)
    def translate(self, node):
        if type(node.target
                ) is Abstraction and node.target.arg_name.name.startswith('_'):
            return '{};\r\n{}{}'.format(self.translate(node.argument),
                                        self.tab(),
                                        self.translate(node.target.body))
        else:
            is_native_var = lambda node, lista: isinstance(
                node.target, Application) and isinstance(
                    node.target.target, TApplication) and isinstance(
                        node.target.target.target, Var
                    ) and node.target.target.target.name in lista

            if is_native_var(node, [
                    '+', '-', '*', '/', '%', '^', '>', '<', '>=', '<=', '==',
                    '!=', '&&', '||', '-->'
            ]):
                return '({} {} {})'.format(
                    self.translate(node.target.argument),
                    self.translate(node.target.target.target),
                    self.translate(node.argument))
            elif is_native_var(node, ['!']):
                return '!{}'.format(self.translate(node.argument))
            else:
                arguments = '' if type(
                    node.argument) is Var and node.argument.name.startswith(
                        '_') else self.translate(node.argument)
                tempNode = node.target
                while isinstance(tempNode, Application):
                    arguments = '{}, {}'.format(
                        self.translate(tempNode.argument), arguments)
                    tempNode = tempNode.target
                return '{}({})'.format(self.translate(tempNode), arguments)

    @dispatch(Abstraction)
    def translate(self, node):
        return '\{}:{} -> {}'.format(node.arg_name,
                                     self.translate(node.arg_type),
                                     self.translate(node.body))

    @dispatch(TAbstraction)
    def translate(self, node):
        return '{}<{}>'.format(self.translate(node.body),
                               self.translate(node.type))

    @dispatch(TApplication)
    def translate(self, node):
        return '{}<{}>'.format(self.translate(node.target),
                               self.translate(node.argument))

    @dispatch(Definition)
    def translate(self, node):
        self.tab_size += 1

        # Get the abstractions of the function
        abstractions = ''
        tempTypee = node.type
        while isinstance(tempTypee, TypeAbstraction):
            abstractions = '{}, {}'.format(abstractions,
                                           self.translate(tempTypee.name))
            tempTypee = tempTypee.type
        abstractions = '<' + abstractions[2:] + '>' if len(
            abstractions) > 0 else abstractions

        # Get the typee
        typee = '{}:{}'.format(self.translate(tempTypee.arg_name),
                               self.translate(tempTypee.arg_type))
        tempTypee = tempTypee.return_type
        while tempTypee != node.return_type:
            typee = '{}, {}:{}'.format(typee, tempTypee.arg_name,
                                       tempTypee.arg_type)
            tempTypee = tempTypee.return_type

        # Get the return type
        return_type = self.translate(node.return_type)

        if type(node.body) is Var and node.body.name in [
                'native', 'uninterpreted'
        ]:
            return '{}{} : ({}) -> {} = {};'.format(node.name, abstractions,
                                                    typee, return_type,
                                                    self.translate(node.body))
        else:
            tempBody = node.body
            while isinstance(tempBody,
                             Abstraction) or type(tempBody) is TAbstraction:
                tempBody = tempBody.body
            return '{}{} : ({}) -> {} {{\r\n{}{};\r\n}}'.format(
                node.name, abstractions, typee, return_type, self.tab(),
                self.translate(tempBody))

    @dispatch(TypeDeclaration)
    def translate(self, node):
        return 'type {}'.format(
            self.translate(node.name)
        )  # TODO: relembrar que pode os parametros nao estao aqui.

    @dispatch(TypeAlias)
    def translate(self, node):
        return 'type {} as {};'.format(node.name, self.translate(node.type))

    @dispatch(Import)
    def translate(self, node):
        raise Exception('Never happens')

    # ----------------------------------------------------------------------- Types
    @dispatch(BasicType)
    def translate(self, node):
        return str(node)

    @dispatch(AbstractionType)
    def translate(self, node):
        return '\{}:{} -> {}'.format(node.arg_name,
                                     self.translate(node.arg_type),
                                     self.translate(node.return_type))

    @dispatch(RefinedType)
    def translate(self, node):
        return '{{{}:{} | {}}}'.format(node.name, self.translate(node.type),
                                       self.translate(node.cond))

    @dispatch(TypeAbstraction)
    def translate(self, node):
        return '{}<{}>'.format(self.translate(node.type), node.name)

    @dispatch(TypeApplication)
    def translate(self, node):
        return '{}<{}>'.format(self.translate(node.target),
                               self.translate(node.argument))

    @dispatch(object)
    def translate(self, node):
        raise Exception('Unknown node during translation:', type(node), node)

    def tab(self):
        return ' ' * 4 * self.tab_size


def is_statement(node):
    return isinstance(node, Application) and type(
        node.target) is Abstraction and node.target.arg_name.name.startswith(
            '_')
