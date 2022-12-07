from __future__ import annotations

import z3

s = z3.Solver()
x, y, k = z3.Ints("x y k")
s.add(
    z3.ForAll([x, y],
              z3.Implies(x < 4, z3.Implies(y < 10, z3.And(k > x, k > y)))))
r = s.check()
if r == z3.sat:
    print(s.model())
else:
    print("unsat")

equations = """
x < 4
y < 10
k > x
k > y
"""

import mystic.symbolic as ms

vars = list("xyk")
eqns = ms.simplify(equations, variables=vars)
constrain = ms.generate_constraint(ms.generate_solvers(eqns, vars))
solution = constrain([1, 2])
print(solution)
