from .types import *
from .ast import *


def substitution_expr_in_expr(n, replacement: Node, replaced):
    """ e[e/t] """

    if not issubclass(replacement.__class__, Node):
        print("ooops1", type(replacement))

    #print(""" e[e/t] """, n, replacement, replaced)
    r = lambda x: substitution_expr_in_expr(x, replacement, replaced)
    nty = n.type == None and None or substitution_expr_in_type(
        n.type, replacement, replaced)
    if type(n) is Literal:
        return n
    elif type(n) is Var:
        if n.name == replaced:
            return replacement.with_type(nty)
        else:
            return n
    elif type(n) is If:
        return If(r(n.cond), r(n.then), r(n.otherwise)).with_type(nty)
    elif type(n) is Application:
        return Application(r(n.target), r(n.argument)).with_type(nty)
    elif type(n) is Abstraction:
        return Abstraction(n.arg_name, n.arg_type, r(n.body)).with_type(nty)
    elif type(n) is TApplication:
        arg = substitution_expr_in_type(n.argument, replacement, replaced)
        return TApplication(r(n.target), arg).with_type(nty)
    elif type(n) is TAbstraction:
        return TAbstraction(n.typevar, n.kind, r(n.body)).with_type(nty)
    elif type(n) is Hole:
        return n
    else:
        raise Exception('No substitution rule for {}'.format(n))


def substitution_type_in_expr(n: Node, replacement: Type, replaced):
    """ e[e/T] """

    if not issubclass(replacement.__class__, Type):
        print("ooops2", type(replacement))

    #print(""" e[e/T] """, n, replacement, replaced)
    r = lambda x: substitution_type_in_expr(x, replacement, replaced)
    nty = n.type == None and None or substitution_type_in_type(
        n.type, replacement, replaced)
    if type(n) is Literal:
        return n
    elif type(n) is Var:
        return n
    elif type(n) is If:
        return If(r(n.cond), r(n.then), r(n.otherwise)).with_type(nty)
    elif type(n) is Application:
        return Application(r(n.target), r(n.argument)).with_type(nty)
    elif type(n) is Abstraction:
        return Abstraction(n.arg_name, n.arg_type, r(n.body)).with_type(nty)
    elif type(n) is TApplication:
        targ = substitution_type_in_type(n.argument, replacement, replaced)
        return TApplication(r(n.target), targ).with_type(nty)
    elif type(n) is TAbstraction:
        return TAbstraction(n.typevar, n.kind, r(n.body)).with_type(nty)
    elif type(n) is Hole:
        return n
    else:
        raise Exception('No substitution rule for {}'.format(n))


def substitution_expr_in_type(n: Type, replacement: Node, replaced):
    """ T[e/t] """
    #print(""" T[e/t] """, n, replacement, replaced)

    if not issubclass(replacement.__class__, Node):
        print("ooops3", type(replacement))

    if n == None:
        return n
    r = lambda x: substitution_expr_in_type(x, replacement, replaced)
    re = lambda x: substitution_expr_in_expr(x, replacement, replaced)
    if type(n) is BasicType:
        return n
    elif type(n) is RefinedType:
        return RefinedType(n.name, r(n.type), re(n.cond))
    elif type(n) is ArrowType:
        # TODO: verificar se é possível trocar o arg_name
        return ArrowType(arg_name=n.arg_name,
                         arg_type=r(n.arg_type),
                         return_type=r(n.return_type))
    elif type(n) is TypeApplication:
        return TypeApplication(target=re(n.target), argument=r(n.argument))
    elif type(n) is TypeAbstraction:
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(n.type))
    else:
        raise TypeException("Substitution in type unknown:", n, type(n))


def substitution_type_in_type(n, replacement: Type, replaced):
    """ T[U/V] """
    #print(""" T[U/V] """, n, replacement, replaced)

    if not issubclass(replacement.__class__, Type):
        print("ooops4", type(replacement))

    if n == None:
        return n
    r = lambda x: substitution_type_in_type(x, replacement, replaced)
    if type(n) is BasicType:
        if n.name == replaced:
            return replacement
        else:
            return n
    elif type(n) is RefinedType:
        new_cond = substitution_type_in_expr(n.cond, replacement, replaced)
        return RefinedType(n.name, r(n.type), new_cond)
    elif type(n) is ArrowType:
        return ArrowType(arg_name=n.arg_name,
                         arg_type=r(n.arg_type),
                         return_type=r(n.return_type))
    elif type(n) is TypeApplication:
        return TypeApplication(target=r(n.target), argument=r(n.argument))
    elif type(n) is TypeAbstraction:
        return TypeAbstraction(name=n.name, kind=n.kind, type=r(n.type))
    else:
        raise TypeException("Substitution type/type unknown:", n, type(n))


if __name__ == '__main__':

    from .frontend import expr, typee
    ex = expr.parse_strict
    ty = typee.parse_strict

    t_t = lambda t1, t2, name: substitution_type_in_type(ty(t1), ty(t2), name)
    t_v = lambda t1, t2, name: substitution_expr_in_type(ty(t1), ex(t2), name)
    t_e = lambda t1, t2, name: substitution_expr_in_expr(ex(t1), ex(t2), name)

    def assert_stt(original, new, old, expects):
        repl = t_t(original, new, old)
        exp = ty(expects)
        if repl != exp:
            print("a", repl)
            print("b", exp)
        assert (repl == exp)

    def assert_svt(original, new, old, expects):
        repl = t_v(original, new, old)
        exp = ty(expects)
        if repl != exp:
            print("a", repl)
            print("b", exp)
        assert (repl == exp)

    def assert_sve(original, new, old, expects):
        repl = t_e(original, new, old)
        exp = ex(expects)
        if repl != exp:
            print("a", repl)
            print("b", exp)
        assert (repl == exp)

    """ type in type, basic_type """

    assert_stt("T", "Bool", "T", expects="Bool")
    assert_stt("T", "Bool", "X", expects="T")
    assert_stt("Bool", "Bool", "X", expects="Bool")
    assert_stt("X", "X", "Bool", expects="X")
    """ type in type, refined """

    assert_stt("{x:X where true }",
               "Boolean",
               "X",
               expects="{x:Boolean where true }")
    assert_stt("{x:X where true }",
               "X",
               "Boolean",
               expects="{x:X where true }")
    assert_stt("{x:{y:X where true} where true }",
               "Boolean",
               "X",
               expects="{x:{y:Boolean where true} where true }")
    assert_stt("{x:{y:X where true} where true }",
               "X",
               "Boolean",
               expects="{x:{y:X where true} where true }")
    """ type in type, arrow """

    assert_stt("(x:T) -> T", "X", "T", expects="(x:X) -> X")
    assert_stt("(x:T) -> T", "T", "X", expects="(x:T) -> T")
    assert_stt("(x:T) -> T", "Bool", "X", expects="(x:T) -> T")
    """ type in type, arrow + refined """

    assert_stt("(x:{y: T where true}) -> {z:T where true}",
               "X",
               "T",
               expects="(x:{y: X where true}) -> {z:X where true}")
    assert_stt("(x:X) -> {z:T where true}",
               "X",
               "T",
               expects="(x:X) -> {z:X where true}")
    assert_stt("(x:X) -> {z:T where true}",
               "X",
               "Bool",
               expects="(x:X) -> {z:T where true}")
    """ type in type, tapp """

    assert_stt("(List X)", "Bool", "X", expects="(List Bool)")
    assert_stt("(List X)", "SList", "List", expects="(SList X)")
    assert_stt("(X:(List X)) -> (List X)",
               "Bool",
               "X",
               expects="(X:(List Bool)) -> (List Bool)")
    assert_stt("(X:(List X)) -> (List Y)",
               "Bool",
               "X",
               expects="(X:(List Bool)) -> (List Y)")
    """ type in type, tabs """
    # TODO: this should not be possible
    assert_stt("(X:*) => (List X)", "Y", "X", expects="(X:*) => (List Y)")
    assert_stt("(X:*) => {x:Y where true}",
               "Z",
               "Y",
               expects="(X:*) => {x:Z where true}")
    """ var in type """
    assert_svt("Boolean", "1", "x", expects="Boolean")
    assert_svt("{x:Boolean where x}",
               "true",
               "x",
               expects="{x:Boolean where true}")
    assert_svt("(y:T) -> {x:Boolean where x}",
               "true",
               "x",
               expects="(y:T) -> {x:Boolean where true}")
    assert_svt("(T:*) => {x:T where x}",
               "true",
               "x",
               expects="(T:*) => {x:T where true}")

    assert_svt("{x:Boolean where (x > 0)}",
               "1",
               "x",
               expects="{x:Boolean where (1 > 0)}")

    assert_svt(
        "(a:{x:Boolean where (y > 0)}) -> {z:Boolean where (y > 0)}",
        "1",
        "y",
        expects="(a:{x:Boolean where (1 > 0)}) -> {z:Boolean where (1 > 0)}")
    """ var in expr """
    assert_sve("x", "1", "x", expects="1")
    assert_sve("x", "1", "y", expects="x")
    assert_sve("1", "1", "y", expects="1")
    assert_sve("[[Integer]]", "1", "y", expects="[[Integer]]")
    assert_sve("(1 + 1)", "1", "y", expects="(1 + 1)")
    assert_sve("(1 + y)", "2", "y", expects="(1 + 2)")

    assert_sve("if a then a else a",
               "true",
               "a",
               expects="if true then true else true")
    assert_sve("if a then (b a) else 1",
               "true",
               "a",
               expects="if true then (b true) else 1")

    assert_sve("\\a:Integer -> y", "2", "y", expects="\\a:Integer -> 2")
    assert_sve("T:* => y", "2", "y", expects="T:* => 2")
    assert_sve("y[Boolean]", "2", "y", expects="2[Boolean]")
    assert_sve("a b c", "c", "b", expects="a c c")

    print("Passed all tests")
