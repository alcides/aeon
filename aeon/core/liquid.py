from typing import List


class LiquidTerm(object):
    pass


class LiquidLiteralBool(LiquidTerm):
    value: bool

    def __init__(self, value: bool):
        self.value = value

    def __repr__(self):
        return u"{}".format(self.value)

    def __eq__(self, other):
        return isinstance(other,
                          LiquidLiteralBool) and other.value == self.value


class LiquidLiteralInt(LiquidTerm):
    value: int

    def __init__(self, value: int):
        self.value = value

    def __repr__(self):
        return u"{}".format(self.value)

    def __eq__(self, other):
        return isinstance(other,
                          LiquidLiteralInt) and other.value == self.value


class LiquidVar(LiquidTerm):
    name: str

    def __init__(self, name: int):
        self.name = name

    def __repr__(self):
        return u"{}".format(self.name)

    def __eq__(self, other):
        return isinstance(other, LiquidVar) and other.name == self.name


class LiquidApp(LiquidTerm):
    fun: str
    args: List[LiquidTerm]

    def __init__(self, fun: str, args: List[LiquidTerm]):
        self.fun = fun
        self.args = args

    def __repr__(self):
        return u"{}({})".format(self.fun,
                                ",".join([repr(x) for x in self.args]))

    def __eq__(self, other):
        return (isinstance(other, LiquidApp) and other.fun == self.fun and all(
            (x == y for (x, y) in zip(self.args, other.args))))
