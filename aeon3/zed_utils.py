import z3


class AstRefKey:
    def __init__(self, n):
        self.n = n

    def __hash__(self):
        return self.n.hash()

    def __eq__(self, other):
        return self.n.eq(other.n)

    def __repr__(self):
        return str(self.n)


def askey(n):
    assert isinstance(n, z3.AstRef)
    return AstRefKey(n)


def get_z3_vars(st):
    if type(st) == type(True):
        return []
    r = set()

    def collect(f):
        if z3.is_const(f):
            if f.decl().kind() == z3.Z3_OP_UNINTERPRETED and not askey(f) in r:
                r.add(askey(f))
        else:
            for c in f.children():
                collect(c)

    collect(st)
    return list(r)
