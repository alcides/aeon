"""Typed product candidates for whole-program search.

Each element belongs to one hole's lexical scope. The product is a search
payload, never an Aeon expression: only the fully substituted program reaches
verification or execution.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation, Location
from aeon.utils.name import Name


@dataclass(frozen=True)
class HoleSpec:
    name: Name
    function: Name
    type: Type
    ctx: TypingContext


@dataclass(frozen=True)
class JointCandidate(Term):
    terms: tuple[Term, ...]
    loc: Location = field(default_factory=lambda: SynthesizedLocation("joint synthesis"), compare=False)

    def __str__(self) -> str:
        return "[" + ", ".join(str(term) for term in self.terms) + "]"


class JointSynthesizer(Synthesizer):
    """A grammar backend that can search a heterogeneous product of holes."""

    def synthesize_joint(
        self,
        holes: tuple[HoleSpec, ...],
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> JointCandidate | None:
        raise NotImplementedError
