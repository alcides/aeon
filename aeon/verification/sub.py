from aeon.core.terms import Var
from aeon.core.types import Bottom, Top, t_bool
from aeon.core.substitutions import substitution_in_liquid, substitution_in_type
from aeon.core.liquid import LiquidLiteralBool, LiquidVar
from aeon.verification.vcs import Conjunction, Constraint, Implication, LiquidConstraint
from aeon.core.types import AbstractionType, BaseType, RefinedType, Type

ctrue = LiquidConstraint(LiquidLiteralBool(True))
cfalse = LiquidConstraint(LiquidLiteralBool(False))


def ensure_refined(t: Type) -> RefinedType:
    if isinstance(t, RefinedType):
        return t
    elif isinstance(t, BaseType):
        return RefinedType("singleton_", t, LiquidLiteralBool(True))
    assert False


def implication_constraint(name: str, t: Type, c: Constraint) -> Constraint:
    if isinstance(t, RefinedType):
        ref_subs = substitution_in_liquid(t.refinement, LiquidVar(name),
                                          t.name)
        return Implication(name, t.type, ref_subs, c)
    elif isinstance(t, BaseType):
        return Implication(name, t, LiquidLiteralBool(True), c)
    else:
        return c


def sub(t1: Type, t2: Type) -> Constraint:
    if isinstance(t2, Top) or isinstance(t1, Bottom):
        return ctrue
    if isinstance(t1, BaseType):
        t1 = ensure_refined(t1)
    if isinstance(t2, BaseType):
        t2 = ensure_refined(t2)
    if isinstance(t1, RefinedType) and isinstance(t2, RefinedType):
        if isinstance(t1.type, Bottom) or isinstance(t2.type, Top):
            return ctrue
        elif t1.type == t2.type:
            t2_subs = substitution_in_liquid(t2.refinement, LiquidVar(t1.name),
                                             t2.name)
            return Implication(t1.name, t1.type, t1.refinement,
                               LiquidConstraint(t2_subs))
        else:
            return cfalse
    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        c1 = sub(t2.var_type, t1.var_type)
        c0 = sub(substitution_in_type(t1.type, Var(t2.var_name), t1.var_name),
                 t2.type)
        return Conjunction(
            c1, implication_constraint(t2.var_name, t2.var_type, c0))
    else:
        return cfalse


"""
sub_ = sub
def sub(a, b):
    c = sub_(a, b)
    print("a:", a, "b:", b, "c:", c)
    return c
"""
