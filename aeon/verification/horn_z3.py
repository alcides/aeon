from aeon.core.liquid import LiquidTerm, LiquidApp, LiquidLiteralInt
from z3 import (
    Datatype,
    IntSort,
    Function,
    BoolSort,
    Const,
    set_option,
    Fixedpoint,
    And,
    Implies,
    Ints,
    ForAll,
    Bools,
    SolverFor,
)

# let max max2 x y z = max2 (max2 x y) z
# let f x y = if x > y then x else y
# assert (f (max f x y z) x) = (max f x y z)


LiqTermWDef = Datatype("LiqTermW")
LiqTermWDef.declare("lit", ("v", IntSort()))
LiqTermWDef.declare("lt", ("op1", LiqTermWDef), ("op2", LiqTermWDef))
LiqTermWDef.declare("eq", ("op1", LiqTermWDef), ("op2", LiqTermWDef))
LiqTermW = LiqTermWDef.create()


def reverse_z3(e) -> LiquidTerm:
    if e.sort() == LiqTermW:
        if e.decl() == LiqTermW.lit:
            return LiquidLiteralInt(reverse_z3(e.arg(0)))
        if e.decl() == LiqTermW.lt:
            return LiquidApp("<", [reverse_z3(e.arg(0)), reverse_z3(e.arg(1))])
    elif e.sort() == IntSort():
        return LiquidLiteralInt(int(str(e)))
    else:
        raise Exception("TODO")


evalBool = Function("evalBool", LiqTermW, BoolSort(), BoolSort())
evalInt = Function("evalInt", LiqTermW, IntSort(), BoolSort())

k1 = Const("k1", LiqTermW)
k2 = Const("k2", LiqTermW)

x = Const("x", IntSort())
y = Const("y", IntSort())
z = Const("z", IntSort())
b = Const("b", BoolSort())

fp = Fixedpoint()
fp.register_relation(evalBool)
fp.register_relation(evalInt)

k1e, k2e = Bools("k1e k2e")

fp.declare_var(x, y, k1, k2, b, z, k1e)

fp.rule(evalInt(LiqTermW.lit(x), x))
fp.rule(evalBool(LiqTermW.lt(k1, k2), b), [evalInt(k1, x), evalInt(k2, y), x < y])
fp.rule(evalBool(LiqTermW.eq(k1, k2), b), [evalInt(k1, x), evalInt(k2, y), x == y])


x, v = Ints("x v")
(c,) = Bools("c")
fp.declare_var(x, v, c)
p1 = Implies(c == (0 <= x), Implies(c, Implies(v == x, k1e)))

fp.query(evalBool(k1, k1e), p1)


a = fp.get_answer()
# print(fp.get_ground_sat_answer())
try:
    sol = a.arg(0).arg(1).children()[0]
    r = reverse_z3(sol)
    print(r)
except:
    print("Could not verify")

"""Expr = Datatype("Expr")
Expr.declare("Max")
Expr.declare("f")
Expr.declare("I", ("i", IntSort()))
Expr.declare("App", ("fn", Expr), ("arg", Expr))
Expr = Expr.create()
Max = Expr.Max
I = Expr.I
App = Expr.App
f = Expr.f
Eval = Function("Eval", Expr, Expr, Expr, BoolSort())
"""


"""
# Max max x y z = max (max x y) z
fp.rule(
    x

    Eval(App(App(App(Max, max), x), y), z, r2),
    [Eval(App(max, x), y, r1), Eval(App(max, r1), z, r2)],
)

# f x y = x if x >= y
# f x y = y if x < y
fp.rule(Eval(App(f, I(xi)), I(yi), I(xi)), xi >= yi)
fp.rule(Eval(App(f, I(xi)), I(yi), I(yi)), xi < yi)

print(
    fp.query(
        And(Eval(App(App(App(Max, f), x), y), z, r1), Eval(App(f, x), r1, r2), r1 != r2)
    )
)

print(fp.get_answer())
"""

s = SolverFor("HORN")
print(s)

k_ = Const("k_", LiqTermW)


s.add(evalBool(k_, True))

print(s.check())
