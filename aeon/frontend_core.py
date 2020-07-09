import os
from lark import Lark, Transformer, v_args
from .types import *
from .ast import *


class TreeToCore(Transformer):
    def same(self, args):
        return args[0]

    def program(self, args):
        return Program(args)

    def path_import(self, args):
        return Import(args[1], function=args[0])

    def regular_import(self, args):
        return Import(args[0])

    def type_alias(self, args):
        return TypeAlias(args[0], args[1])

    def type_declaration(self, args):
        return TypeDeclaration(args[0], args[1], ghost_variables=args[1])

    def definition(self, args):
        return Definition(*args)

    # Kind
    def star(self, args):
        return Kind()

    def rec_star(self, args):
        return Kind(*args)

    # Types
    def refined_t(self, args):
        return RefinedType(str(args[0]), args[1], args[2])

    def abstraction_t(self, args):
        return AbstractionType(str(args[0]), args[1], args[2])

    def tabstraction_t(self, args):
        return TypeAbstraction(*args)

    def simple_t(self, args):
        return BasicType(*args)

    def tapplication_t(self, args):
        return TypeApplication(*args)

    # Expressions

    def minus(self, args):
        return Application(Application(Var("-"), Literal(0.0, t_f)), args[0])

    def let_e(self, args):
        abst = Abstraction(str(args[0]), args[1], args[3])
        return Application(abst, args[2])

    def if_e(self, args):
        return If(*args)

    def nnot(self, args):
        return Application(Var("!"), args[0])

    def binop_eq(self, args):
        return self.binop(args, "==")

    def binop_neq(self, args):
        return self.binop(args, "!=")

    def binop_and(self, args):
        return self.binop(args, "&&")

    def binop_or(self, args):
        return self.binop(args, "||")

    def binop_lt(self, args):
        return self.binop(args, "<")

    def binop_le(self, args):
        return self.binop(args, "<=")

    def binop_gt(self, args):
        return self.binop(args, ">")

    def binop_ge(self, args):
        return self.binop(args, ">=")

    def binop_imp(self, args):
        return self.binop(args, "-->")

    def binop_plus(self, args):
        return self.binop(args, "+")

    def binop_minus(self, args):
        return self.binop(args, "-")

    def binop_mult(self, args):
        return self.binop(args, "*")

    def binop_div(self, args):
        return self.binop(args, "/")

    def binop_mod(self, args):
        return self.binop(args, "%")

    def binop(self, args, op):
        if op in ["==", "!=", "+", "-", "*", "/", "<", ">", "<=", ">="]:
            return Application(
                Application(TApplication(Var(op), t_delegate), args[0]),
                args[1])
        return Application(Application(Var(op), args[0]), args[1])

    def tapplication_e(self, args):
        return TApplication(*args)

    def application_e(self, args):
        return Application(*args)

    def abstraction_e(self, args):
        return Abstraction(*args)

    def tabstraction_e(self, args):
        return TAbstraction(*args)

    def hole(self, args):
        return Hole(args[0])

    def var(self, args):
        return Var(str(args[0]))

    def fitness_annotation(self, args):
        return Var(str(args[0]))

    def int_lit(self, args):
        return Literal(int(args[0]),
                       type=refined_value(int(args[0]), t_i, "_v"))

    def float_lit(self, args):
        return Literal(float(args[0]),
                       type=refined_value(float(args[0]), t_f, "_v"))

    def bool_lit(self, args):
        value = str(args[0]) == "true"
        return Literal(value, type=refined_value(value, t_b, "_v"))

    def string_lit(self, args):
        v = str(args[0])[1:-1]
        return Literal(str(v), type=refined_value(str(v), t_s, "_v"))


def mk_parser(rule="start"):
    return Lark.open(
        "aeon/aeon_core.lark",
        parser='lalr',
        #lexer='standard',
        start=rule,
        transformer=TreeToCore())


cached_imports = []


def resolve_imports(p : Program, base_path=lambda x: x):
    n_p = []
    for n in p.declarations:
        if isinstance(n, Import):
            fname = n.name
            path = ""
            while fname.startswith(".."):
                fname = fname[2:]
                path = path + "../"
            path = path + fname.replace(".", "/")
            path = os.path.realpath(base_path(path))
            if path not in cached_imports:
                cached_imports.append(path)
                ip = parse(path)
                n_p.extend(ip.declarations)
        else:
            n_p.append(n)
    return n_p


p = mk_parser()
typee = mk_parser("type")
expr = mk_parser("expression")
kind = mk_parser("kind")


def parse(fname):
    txt = open(fname).read()
    p = mk_parser().parse(txt)
    p = resolve_imports(p,
                        base_path=lambda x: os.path.join(
                            os.path.dirname(fname), "{}.{}".format(x, "ae2")))
    return Program(p)


if __name__ == "__main__":
    import os
    path = "examples/aeon_core/"
    for fn in os.listdir(path):
        print(fn)
        with open(path + fn, "r") as f:
            print(p.parse(f.read()))
