from ..types import TypingContext

from .kinding import check_kind, synth_kind
from .typing import TypeCheckingError, check_program, check_type, synth_type
from .subtyping import SubtypingException, is_subtype
from .zed import entails, is_satisfiable, zed_get_integer_where


def get_integer_where(ctx: TypingContext, name: str, cond):
    return zed_get_integer_where(ctx, name, cond)
