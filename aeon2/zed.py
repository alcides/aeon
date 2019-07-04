import sys
from functools import reduce

from .typestructure import *
import z3


class Zed(object):
    def __init__(self):
        self.vars = {}
        self.solver = z3.Solver()
        self.current_context = None
        self.current_typecontext = None

    def copy_assertions(self):
        return self.solver.assertions()

    def enter_context(self):
        self.solver.push()

    def exit_context(self):
        self.solver.pop()

    def translate_type(self, t):
        acc = True
        print("Type:", t)
        if t.refinements:
            for ref in t.refinements:
                return z3.And(acc, self.translate_expr(ref))
        return acc

    def translate_expr(self, n):
        if type(n) is Operator:
            if n.name == "==":
                return self.translate_expr(
                    n.arguments[0]) == self.translate_expr(n.arguments[1])
        elif type(n) is Atom:
            t = self.current_context.find(n.name)
            if t:
                return self.translate_type(t)
            else:
                raise Exception("Unknown variable {} ({})".format(n, type(n)))
        elif type(n) is Argument:
            self.typecheck_argument(n)
        elif type(n) is Literal:
            return self.make_literal(n.value)
            self.typecheck_literal(n)
        elif type(n) is Invocation:
            self.typecheck_invocation(n, expects)
        else:
            raise Exception("Unknown expr node {} ({})".format(n, type(n)))

    def is_subtype(self, t1, t2, context, typecontext):

        self.current_context = context
        self.current_typecontext = typecontext
        subtype = self.translate_type(t1)
        supertype = self.translate_type(t2)
        self.current_context = None
        self.current_typecontext = None

        self.solver.add(z3.Not(z3.Implies(subtype, supertype)))

        ver = self.solver.check()
        if ver == z3.unsat:
            return True
        elif ver == z3.sat:
            return False
        else:
            print("Unknown verification in function return")
            return True

    def make_literal(self, t, v):
        """ Creates a literal value for a given variable

        Ex: (x:Integer where x == 1)

        1 will be a literal here.
        """
        if t.basic == 'String':
            literal_value = z3.StringVal(v)
        else:
            literal_value = v
        return literal_value

    def z3_type_constructor(self, t):
        """ Returns the constructor of Z3 for a given type

        For instance, for type Double

        1.0 : Double

        This function will return z3.Real, such as

        z3.Real(1.0) will be a valid z3 literal.

        """
        if t == BasicType('Double'):
            return z3.Real
        elif t == BasicType('Float'):
            return z3.Real
        elif t == BasicType('Integer'):
            return z3.Int
        elif t == BasicType('Boolean'):
            return z3.Bool
        elif t == BasicType('String'):
            return z3.String
        else:
            return z3.Int
            raise Exception("Unknown Type Constructor", t)


zed = Zed()
