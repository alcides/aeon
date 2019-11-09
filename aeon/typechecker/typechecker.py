from ..types import TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b, t_delegate
from ..ast import Var, TAbstraction, TApplication, Application, Abstraction, Literal, Node


def check(ctx: TypingContext, n: Node, expected: Type):
    return True
