"""Session-owned solver and translation caches, separate from SMT translation."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from z3 import Solver
from z3.z3 import SortRef

from aeon.compilation.session import current_session
from aeon.core.liquid import LiquidTerm
from aeon.core.types import AbstractionType, TypeConstructor
from aeon.utils.name import Name
from aeon.verification.trace import Status


@dataclass
class VerificationState:
    timeout_ms: int = field(default_factory=lambda: current_session().options.smt_timeout_ms)
    solver: Solver | None = field(default=None, init=False, repr=False)
    validity: dict[str, bool] = field(default_factory=dict)
    proved_clauses: dict[str, bool] = field(default_factory=dict)
    statuses: dict[str, tuple[Status, str | None]] = field(default_factory=dict)
    ple: dict[tuple[int, int], tuple[LiquidTerm, dict[str, tuple[tuple[Name, ...], LiquidTerm]], LiquidTerm]] = field(
        default_factory=dict
    )
    sorts: dict[str, SortRef] = field(default_factory=dict)
    variables: dict[int, tuple[dict[str, TypeConstructor], dict[str, Any]]] = field(default_factory=dict)
    functions: dict[int, tuple[dict[str, AbstractionType], dict[str, Any]]] = field(default_factory=dict)
    function_symbols: dict[tuple[str, int, int], tuple[AbstractionType, dict[str, SortRef], Any]] = field(
        default_factory=dict
    )
    sort_sets: dict[tuple[str, ...], dict[str, SortRef]] = field(default_factory=dict)
    array_literals: dict[tuple[tuple[int, int], ...], Any] = field(default_factory=dict)
    array_elements: dict[tuple[int, int], tuple[Any, tuple[Any, ...] | None]] = field(default_factory=dict)
    array_reads: dict[tuple[tuple[int, int], tuple[int, int] | tuple[str, int]], tuple[Any, Any, Any]] = field(
        default_factory=dict
    )
    reflected_calls: dict[tuple[Name, tuple[Name, ...], LiquidTerm, tuple[LiquidTerm, ...]], LiquidTerm] = field(
        default_factory=dict
    )
    generation: int = 0

    def get_solver(self) -> Solver:
        if self.solver is None:
            self.solver = Solver()
            self.solver.set(timeout=self.timeout_ms)
        return self.solver
