"""Immutable observations, regularized risk, and auditable noisy-search reports."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import math
import os

from aeon.synthesis.api import UnsupportedSynthesisGoal

Scalar = bool | int | float | str


def scalar(value) -> bool:
    return type(value) in (bool, int, float, str) and (type(value) is not float or math.isfinite(value))


def same_value(left, right) -> bool:
    return type(left) is type(right) and left == right


@dataclass(frozen=True)
class Observation:
    id: int
    inputs: tuple[Scalar, ...]
    expected: Scalar


@dataclass(frozen=True)
class Dataset:
    rows: tuple[Observation, ...]

    @classmethod
    def from_pairs(cls, pairs, arity: int):
        if not pairs:
            raise UnsupportedSynthesisGoal("noisy requires a nonempty scalar I/O dataset")
        rows = []
        for index, pair in enumerate(pairs):
            if not isinstance(pair, (list, tuple)) or len(pair) != 2:
                raise UnsupportedSynthesisGoal(f"Malformed noisy observation {index}")
            inputs, expected = pair
            if not isinstance(inputs, (list, tuple)) or len(inputs) != arity:
                raise UnsupportedSynthesisGoal(f"Wrong input arity in noisy observation {index}")
            if not all(scalar(v) for v in (*inputs, expected)):
                raise UnsupportedSynthesisGoal(f"Observation {index} requires finite scalar values")
            rows.append(Observation(index, tuple(inputs), expected))
        return cls(tuple(rows))


@dataclass(frozen=True)
class Config:
    regularization: float = 0.05
    initial_sample: int = 2
    rounds: int = 8
    candidates_per_round: int = 32
    archive_size: int = 128
    history_size: int = 16
    cache_size: int = 512
    max_rows: int = 10_000
    max_depth: int = 3
    max_expansions: int = 3000
    max_worklist: int = 5000
    call_timeout: float = 1.0
    sampler: str = "adaptive"
    exact_subsets: int = 2000
    exchange_trials: int = 256

    def __post_init__(self):
        if not math.isfinite(self.regularization) or self.regularization < 0:
            raise UnsupportedSynthesisGoal("AEON_NOISY_LAMBDA must be finite and nonnegative")
        if not math.isfinite(self.call_timeout) or self.call_timeout <= 0:
            raise UnsupportedSynthesisGoal("AEON_NOISY_CALL_TIMEOUT must be finite and positive")
        for name in (
            "initial_sample",
            "rounds",
            "candidates_per_round",
            "archive_size",
            "history_size",
            "cache_size",
            "max_depth",
            "max_expansions",
            "max_worklist",
            "exact_subsets",
            "exchange_trials",
            "max_rows",
        ):
            if type(getattr(self, name)) is not int or getattr(self, name) <= 0:
                raise UnsupportedSynthesisGoal(f"noisy {name} must be a positive integer")
        if self.sampler not in ("adaptive", "uniform", "full"):
            raise UnsupportedSynthesisGoal("AEON_NOISY_SAMPLER must be adaptive, uniform or full")

    @classmethod
    def from_env(cls):
        options = {}
        names = {"regularization": "LAMBDA", "call_timeout": "CALL_TIMEOUT"}
        for name in cls.__dataclass_fields__:
            value = os.environ.get("AEON_NOISY_" + names.get(name, name.upper()))
            if value is not None:
                try:
                    options[name] = value if name == "sampler" else float(value) if name in names else int(value)
                except ValueError as exc:
                    raise UnsupportedSynthesisGoal(f"Invalid noisy configuration for {name}") from exc
        return cls(**options)


@dataclass(frozen=True)
class Residual:
    observation_id: int
    expected: Scalar
    actual: Scalar


@dataclass(frozen=True)
class SamplingRound:
    sample: tuple[int, ...]
    discrepancy: float
    method: str
    history_count: int


@dataclass(frozen=True)
class Report:
    empirical_error: float
    regularization: float
    regularization_term: float
    complexity: int
    objective: float
    row_count: int
    residuals: tuple[Residual, ...]
    rounds: tuple[SamplingRound, ...]
    seed: int
    stop_reason: str
    candidates_generated: int
    candidates_validated: int
    candidates_fully_scored: int
    invalid_candidates: int
    row_evaluations: int
    elapsed_seconds: float
    generator: str = "bounded native enumeration (approximate)"

    def as_dict(self):
        return {"backend": "noisy", **asdict(self)}


def risk(losses, indices) -> float:
    return sum(losses[i] for i in indices) / len(indices)
