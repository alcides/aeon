from typing import Any, Callable, override
from time import monotonic_ns

from aeon.core.liquid import LiquidLiteralBool, LiquidTerm
from aeon.core.terms import Literal, Term
from aeon.core.types import RefinedType, Type, TypeConstructor
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.core.terms import Hole

import z3

from aeon.verification.smt import translate_liq


def get_elapsed_time(start_time: float) -> float:
    """The elapsed time since the start in seconds."""
    return (monotonic_ns() - start_time) * 0.000000001


def is_better(a: list[float], b: list[float] | None, minimize: list[bool]) -> bool:
    if b is None:
        return True
    wins = 0
    losses = 0
    for ai, bi, min in zip(a, b, minimize):
        if min:
            if ai <= bi:
                wins += 1
            else:
                losses += 1
        else:
            if ai >= bi:
                wins += 1
            else:
                losses += 1
    return wins - losses > 0


def handle_base_type(type: Type) -> tuple[Any, Type, Callable[[Any], Any], Name, LiquidTerm]:
    var: Any
    vtype: Type
    reverse: Callable[[Any], Any]
    match type:
        case TypeConstructor(Name("Bool", _)):
            var = z3.Bool("var")
            vtype = TypeConstructor(Name("Bool", -1))
            reverse = bool
        case TypeConstructor(Name("Int", _)):
            var = z3.Int("var")
            vtype = TypeConstructor(Name("Int", -1))
            reverse = int
        case RefinedType(name, btype, ref):
            var, vtype, reverse, _, _ = handle_base_type(btype)
            return var, vtype, reverse, name, ref
        case _:
            raise NotImplementedError()
    return var, vtype, reverse, Name("_", -1), LiquidLiteralBool(True)


class SMTSynthesizer(Synthesizer):
    @override
    def synthesize(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> Term:
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)
        fail_term: Term = Hole(Name("sorry", -1))

        print("ty", type)

        match handle_base_type(type):
            case (var, vtype, reverse, name, cond):
                solver = z3.Solver()
                solver.add(translate_liq(cond, {str(name): var}))

                match solver.check():
                    case z3.z3.sat:
                        m = solver.model()
                        if var in m:
                            return Literal(value=reverse(m[var]), type=vtype)
                        else:
                            return fail_term
                    case _:
                        return fail_term

            case _:
                return fail_term
