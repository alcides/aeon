"""Inference-only optimized grammar enumeration through Aeon's normal validator."""

from __future__ import annotations

from dataclasses import dataclass, asdict
import os
from pathlib import Path
from time import monotonic

from loguru import logger
from aeon.core.multiplicity import MOmega
from aeon.core.terms import Abstraction
from aeon.core.types import AbstractionType
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.modules.native_search import drive_candidates, make_skip
from aeon.synthesis.scope import shadow_fitness_helpers, without_excluded_names
from .core import sort_of, to_core
from .grammar import Grammar, base_productions
from .profile import DEFAULT_PROFILE, load


@dataclass
class Stats:
    profile_sha256: str = ""
    stdlib_sha256: str = ""
    macros_available: int = 0
    productions: int = 0
    candidates: int = 0
    validation_failures: int = 0
    estimated_rank_bound: int = 0
    elapsed: float = 0
    stop: str = "not_started"
    original_grammar_fallback: bool = False


class AmazeSynthesizer(Synthesizer):
    def __init__(self, profile_path=None, *, seed=0, max_cost=9, max_candidates=100_000):
        self.profile_path = Path(profile_path or os.environ.get("AEON_AMAZE_PROFILE", str(DEFAULT_PROFILE)))
        self.seed = seed
        self.max_cost = max_cost
        self.max_candidates = max_candidates
        self.stats = Stats()

    def synthesize(self, ctx, type, validate, evaluate, fun_name, metadata, budget=60, ui=None, output_value=None):
        from aeon.synthesis.uis.api import SynthesisUI

        start = monotonic()
        self.stats = Stats(stop="loading_profile")
        try:
            profile = load(self.profile_path)
        except (ValueError, KeyError, TypeError) as exc:
            raise UnsupportedSynthesisGoal(str(exc)) from exc
        ctx = without_excluded_names(shadow_fitness_helpers(ctx, metadata))
        wrappers = []
        while isinstance(type, AbstractionType):
            if type.multiplicity is not MOmega:
                raise UnsupportedSynthesisGoal("amaze does not support linear/erased/polymorphic function parameters")
            try:
                sort_of(type.var_type, refinements=True)
            except ValueError as exc:
                raise UnsupportedSynthesisGoal(str(exc)) from exc
            wrappers.append(type.var_name)
            ctx = ctx.with_var(type.var_name, type.var_type)
            type = type.type
        try:
            goal = sort_of(type, refinements=True)
        except ValueError as exc:
            raise UnsupportedSynthesisGoal(str(exc)) from exc
        skip = make_skip(fun_name, metadata)
        variables, sorts = [], []
        for name, ty in ctx.concrete_vars():
            if skip(name):
                continue
            try:
                sort = sort_of(ty, refinements=True)
            except ValueError:
                continue  # Opaque helpers/polymorphic signatures are not mined.
            variables.append(name)
            sorts.append(sort)
        grammar = Grammar(base_productions(tuple(sorts)) + profile.macros)
        self.stats = Stats(
            profile.sha256, profile.stdlib_sha256, len(profile.macros), len(grammar.productions), stop="searching"
        )
        used_macros = set()
        deadline = start + max(0, budget)

        def candidates():
            for expr, cost, used in grammar.enumerate(goal, self.max_cost, self.max_candidates, deadline):
                self.stats.candidates += 1
                self.stats.estimated_rank_bound = grammar.rank_bound(goal, cost)
                used_macros.update(i for i in used if i.startswith("macro:"))
                term = to_core(expr, tuple(variables))
                for name in reversed(wrappers):
                    term = Abstraction(name, term)
                yield term

        def checked(term):
            result = validate(term)  # includes whole-program/refinement/ownership checks
            self.stats.validation_failures += not result
            return result

        try:
            result = drive_candidates(
                candidates(),
                checked,
                evaluate,
                fun_name,
                metadata,
                max(0, deadline - monotonic()),
                ui or SynthesisUI(),
                self.seed,
            )
            self.stats.stop = (
                "solved"
                if result is not None
                else "budget"
                if monotonic() >= deadline
                else "candidate_limit"
                if self.stats.candidates >= self.max_candidates
                else "cost_limit"
            )
            if result is None:
                raise SynthesisNotSuccessful(f"amaze: {self.stats.stop} after {self.stats.candidates} candidates")
            return result
        finally:
            self.stats.elapsed = monotonic() - start
            logger.info("AMaze: {}", asdict(self.stats) | {"macros_enumerated": sorted(used_macros)})
