from z3 import *

"""
Example of isl performing Refined Type Checking

ex:

create(n:Integer) -> _:Array<type=T,size=n> where { 0 <= n }
get(arr:Array<type=T, size=n>, i:Integer) -> r:T where { 0 <= i < n }
plus(int k) -> m:Integer where { m = k + 1 }

let a = create(10)
let b = 10
print(get(a, b))
let c = plus(b)
print(get(a, c))


type_of = {
    'create': {
        'pre': [
            Set("[create_def_n] -> { : 0 <= create_def_n }")
        ],
        'pos': [
            Set("[create_def_n, create_def_return_n] -> { : create_def_n = create_def_return_n }")
        ]
    },
    'get':  {
        'pre': [
            Set("[get_def_arr_n, get_def_i] -> { : 0 <= get_def_i < get_def_arr_n }")
        ],
        'pos': []
    },
    'plus': {
        'pre': [],
        'pos': [
               Set("[plus_def_i, plus_return_n] -> { : plus_def_i + 1 = plus_return_n }")
        ]
    }
}
"""

types = {
    'create': (
        lambda args: 0 <= args[0],
        lambda ret, args: ret == args[0]
    ),
    'get': (
        lambda args: And(0 <= args[1], args[1] < args[0]),
        lambda ret, args: None
    ),
    'plus': (
        lambda args: None,
        lambda ret, args: args[0] + 1 == ret
    )
}

class TypeChecker:
    def __init__(self):
        self.solver = Solver()
        self.c = 0

    def nvar(self, t):
        self.c += 1
        return t("_node_{}".format(self.c))

    def state(self, stmt):
        self.verify(stmt)

    def tc(self, fun, args):
        # Pre conditions
        cond = types[fun][0](args)
        if cond != None:
            self.verify(cond)

        ret = self.nvar(Int)

        pcond = types[fun][1](ret, args)
        if pcond != None:
            self.verify(pcond)
        return ret


    def verify(self, *stmts):
        print("Checking ====================")
        self.solver.push()
        for st in stmts:
            self.solver.add(st)
        r = self.solver.check()
        if r == sat:
            print self.solver.model()
        elif r == unsat:
            print("Type Error in", stmts)
            print(self.solver.assertions())
            self.solver.pop()
        else:
            print("Unknown")
            self.solver.pop()
        return r

t = TypeChecker()


lit_10 = t.nvar(Int)
t.state(lit_10 == 10)

a_array_size = t.tc("create", [lit_10]) # method

b = t.nvar(Int)
t.state(b == 9)

_ = t.tc("get", [a_array_size, b])

c = t.tc("plus", [b])

_ = t.tc("get", [a_array_size, c])



z = Real("z")

t.state( z <= 3.0)

m = t.solver.model()

#t.state( z == 4.0)

