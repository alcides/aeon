class Type(object):
    def __init__(self, t, tpars=None):
        self.t = t
        self.tpars = tpars if tpars else []

    def __str__(self):
        return "{}{}".format(self.t, "" if not self.tpars else "<" + ", ".join(map(str, self.tpars)) + ">")

    def __repr__(self):
        return str(self)

    def __eq__(self, o):
        if not o:
            return False
        if type(o) != Type:
            return False
        return self.t == o.t and self.tpars == o.tpars

class FType(object):
    def __init__(self, argtypes, rtype):
        self.argtypes = argtypes
        self.rtype = rtype

    def __str__(self):
        return "{} -> {}".format(", ".join(map(str,self.argtypes)), str(self.rtype))

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if type(other) != FType:
            return False
        return self.argtypes == other.argtypes and self.rtype == other.rtype


# defaults
t_v = Type('Void')
t_n = Type('Object')
t_i = Type('Integer')
t_b = Type('Boolean')
t_f = Type('Float')
