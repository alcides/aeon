from abc import ABC
from typing import TYPE_CHECKING, Callable, Optional

from aeon.typechecking.context import TypingContext

from aeon.backend.evaluator import EvaluationContext
from aeon.core.types import Type
from aeon.core.terms import Term
from aeon.utils.name import Name

from aeon.synthesis.uis.api import SynthesisUI
from aeon.decorators.api import Metadata

if TYPE_CHECKING:
    from aeon.synthesis.evaluation_pool import Computation, EvalPrimitives


class SynthesisError(Exception):
    pass


class SynthesisNotSuccessful(SynthesisError):
    pass


class UnknownSynthesizerError(SynthesisError):
    """Raised when ``-s``/``--synthesizer`` names a backend that does not exist."""

    def __init__(self, synthesizer_id: str):
        self.synthesizer_id = synthesizer_id
        super().__init__(f"Unknown synthesizer: {synthesizer_id}")


class TimeoutInEvaluationException(SynthesisError):
    pass


class ErrorInSynthesis(SynthesisError):
    def __init__(self, inner_exception: Exception, msg: str):
        self.inner_exception = inner_exception
        self.msg = msg


class Synthesizer(ABC):
    def computations(self, primitives: "EvalPrimitives") -> dict[str, "Computation"]:
        """Declare the per-candidate computations this backend wants the shared
        evaluation pool to run. The default is just the objective ``fitness``
        (exposed as the ``evaluate`` argument); a backend that also reads the
        candidate's output (e.g. to cluster by it) adds ``"output"``, and any
        other named computation it composes from ``primitives``. What a backend
        *does* with each result stays inside the backend."""
        return {"fitness": primitives.fitness}

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
        output_value: Callable[[Term], object] | None = None,
    ) -> Term: ...


class ProgramSynthesizer(ABC):
    """A synthesizer that fills *all* of a program's holes jointly.

    The per-hole :class:`Synthesizer` interface sees one hole at a time, so it
    cannot optimise holes that interact (e.g. several ``Float`` constants that
    jointly minimise one objective). A ``ProgramSynthesizer`` instead receives
    the whole program and the full list of hole targets and returns a mapping
    from every hole name to its synthesised term. ``synthesize_holes``
    dispatches to this entry point when the chosen synthesizer is one.
    """

    def synthesize_program(
        self,
        ctx: TypingContext,
        ectx: EvaluationContext,
        term: Term,
        targets: list[tuple[Name, list[Name]]],
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> dict[Name, Optional[Term]]: ...
