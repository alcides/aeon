"""Tokenizer-aware rejection sampling, before any model/token commitment."""

from __future__ import annotations

from dataclasses import dataclass
import math
import random
from time import monotonic
from typing import Callable, Protocol, Sequence

from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.modules.type_constrained.prefix import PrefixEngine, State, Status


class DecodingExhausted(SynthesisNotSuccessful):
    category = "resource_exhausted"


class DecodingCancelled(SynthesisNotSuccessful):
    category = "cancelled"


@dataclass(frozen=True)
class Decoded:
    # Full generated text, not decode([id]) or an assumed append-only suffix.
    text: str
    stable: bool = True


class TokenAdapter(Protocol):
    eos_ids: frozenset[int]
    special_ids: frozenset[int]

    def start(self, prompt: str) -> None: ...
    def scores(self) -> Sequence[float]: ...
    def preview(self, token: int) -> Decoded: ...
    def commit(self, token: int) -> None: ...


@dataclass
class Statistics:
    tokens: int = 0
    rejected_tokens: int = 0
    unknown_tokens: int = 0
    oracle_seconds: float = 0.0
    attempts: int = 0
    validation_passed: int = 0
    validation_failed: int = 0


@dataclass(frozen=True)
class Sampling:
    max_tokens: int = 128
    max_probes: int = 4096
    initial_top_k: int = 32
    temperature: float = 0.0

    def __post_init__(self):
        if min(self.max_tokens, self.max_probes, self.initial_top_k) <= 0:
            raise ValueError("sampling limits must be positive")
        if not math.isfinite(self.temperature) or self.temperature < 0:
            raise ValueError("temperature must be finite and nonnegative")


def check_deadline(deadline: float, cancelled: Callable[[], bool]) -> None:
    if cancelled():
        raise DecodingCancelled("type-constrained decoding cancelled")
    if monotonic() >= deadline:
        raise DecodingExhausted("type-constrained decoding wall-clock budget exhausted")


def decode(
    adapter: TokenAdapter,
    engine: PrefixEngine,
    prompt: str,
    deadline: float,
    rng: random.Random,
    settings: Sampling = Sampling(),
    stats: Statistics | None = None,
    cancelled: Callable[[], bool] = lambda: False,
) -> str:
    stats = stats if stats is not None else Statistics()
    check_deadline(deadline, cancelled)
    adapter.start(prompt)
    check_deadline(deadline, cancelled)
    state = State()
    for _ in range(settings.max_tokens):
        check_deadline(deadline, cancelled)
        scores = adapter.scores()
        check_deadline(deadline, cancelled)
        # A Gumbel ranking is weighted sampling without replacement. Taking its
        # first LIVE token is rejection sampling from the full allowed softmax,
        # rather than renormalizing an arbitrarily truncated top-k distribution.
        ranked = []
        for token, score in enumerate(scores):
            if not math.isfinite(score):
                continue
            priority = score
            if settings.temperature:
                priority = score / settings.temperature - math.log(-math.log(max(rng.random(), 1e-300)))
            ranked.append((priority, token))
        ranked.sort(reverse=True)
        committed = False
        probes = 0
        for offset in range(0, len(ranked), settings.initial_top_k):
            for _, token in ranked[offset : offset + settings.initial_top_k]:
                check_deadline(deadline, cancelled)
                if probes >= settings.max_probes:
                    raise DecodingExhausted("token probe bound exhausted; increase AEON_TC_MAX_PROBES")
                probes += 1
                began = monotonic()
                if token in adapter.eos_ids:
                    accepting = engine.is_accepting(state, deadline)
                    stats.oracle_seconds += monotonic() - began
                    if accepting:
                        check_deadline(deadline, cancelled)
                        adapter.commit(token)
                        stats.tokens += 1
                        return state.text
                elif token not in adapter.special_ids:
                    decoded = adapter.preview(token)
                    if decoded.stable and decoded.text != state.text:
                        trial = State(decoded.text)
                        result = engine.completion_status(trial, deadline)
                        stats.oracle_seconds += monotonic() - began
                        if result.status is Status.LIVE:
                            check_deadline(deadline, cancelled)
                            adapter.commit(token)
                            state = trial
                            stats.tokens += 1
                            committed = True
                            break
                        if result.status is Status.UNKNOWN:
                            stats.unknown_tokens += 1
                    else:
                        # Unfinished UTF-8 or a non-progress token cannot be
                        # certified by the character oracle. Never guess LIVE.
                        stats.unknown_tokens += 1
                stats.rejected_tokens += 1
            if committed:
                break
        if not committed:
            raise DecodingExhausted(
                "no certified continuation in this tokenizer/search budget; this is not a proof of uninhabitability"
            )
    raise DecodingExhausted("token budget exhausted before accepting EOS; increase AEON_TC_MAX_TOKENS")
