from aeon.core.terms import Var
from z3.z3 import is_sub
from aeon.core.substitutions import substitution_in_liquid, substitution_in_type
from aeon.verification.vcs import Implication, LiquidConstraint
from aeon.core.liquid import LiquidLiteralBool, LiquidVar
from typing import Union
from aeon.core.types import AbstractionType, BaseType, RefinedType, Type
from aeon.typing.context import TypingContext, VariableBinder
from aeon.typing.typeinfer import InferenceContext
from aeon.typing.entailment import entailment


def ensure_refined(t: Type) -> RefinedType:
    if isinstance(t, RefinedType):
        return t
    elif isinstance(t, AbstractionType):
        assert False  # Should not happen
    elif isinstance(t, BaseType):
        return RefinedType("_", t, LiquidLiteralBool(True))
    assert False


def is_subtype(ctx: TypingContext, sub: Union[InferenceContext, Type],
               sup: Union[InferenceContext, Type]):
    if isinstance(sub, Type):
        subc = InferenceContext(sub)
    else:
        subc = sub
        sub = subc.type
    if isinstance(sup, Type):
        supc = InferenceContext(sup)
    else:
        supc = sup
        sup = supc.type

    if isinstance(sub, AbstractionType) and isinstance(sup, AbstractionType):
        nctx = VariableBinder(ctx, sup.var_name, sup.var_type)
        sub_subs = substitution_in_type(sub.type, Var(sup.var_name),
                                        sub.var_name)
        return is_subtype(ctx, sup.var_type, sub.var_type) and is_subtype(
            nctx, sub_subs, sup.type)
    elif isinstance(sub, BaseType) and isinstance(sup, BaseType):
        return sub == sup
    elif isinstance(sub, RefinedType) or isinstance(sup, RefinedType):
        rsub = ensure_refined(sub)
        rsup = ensure_refined(sup)
        if rsub.type != rsup.type:
            return False
        sup_subs = substitution_in_liquid(rsup.refinement,
                                          LiquidVar(rsub.name), sup.name)
        return entailment(
            ctx,
            Implication(rsub.name, rsub.type, rsub.refinement,
                        LiquidConstraint(sup_subs)))
    return False
