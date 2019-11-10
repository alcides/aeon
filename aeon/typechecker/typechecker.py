from ..types import TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b, t_delegate
from ..ast import Var, TAbstraction, TApplication, Application, Abstraction, Literal, Node


def synth_type(ctx: TypingContext, n: Node) -> Type:
    """ Γ ⸠ e => T """


def check_type(ctx: TypingContext, n: Node, expected: Type):
    """ Γ ⸠ e <= T """
    return True
