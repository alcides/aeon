"""ReGuS adapter: goals and execution observations come from the Aeon problem."""

from __future__ import annotations

from collections.abc import Callable
from time import monotonic

from aeon.core.terms import Term
from aeon.core.types import AbstractionType, Type, TypeConstructor, refined_to_unrefined_type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import (
    ErrorInSynthesis,
    InvalidIndividualException,
    Synthesizer,
    SynthesisNotSuccessful,
    TimeoutInEvaluationException,
    UnsupportedSynthesisGoal,
)
from aeon.synthesis.evaluation_pool import EvalPrimitives, Computation
from aeon.synthesis.modules.regus.model import Plan, decode
from aeon.synthesis.modules.regus.search import Config, Stats, search, utility
from aeon.synthesis.pareto import minimize_flags_from_goals, pick_pareto_member, update_pareto_front, ParetoEntry
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


class ReGuSSynthesizer(Synthesizer):
    def __init__(self, seed: int = 0, config: Config = Config()):
        self.seed = seed
        self.config = config
        self.stats = Stats()

    def evaluation_timeout(self, default: float) -> float:
        return max(default, self.config.evaluation_timeout)

    def computations(self, primitives: EvalPrimitives) -> dict[str, Computation]:
        feature = primitives.feature

        def observe(program: Term):
            value = feature(program)
            # A deferred feature avoids computing traces for backends that
            # only request fitness. Invoke the thunk inside the timed worker.
            return value(0) if callable(value) else value

        return {"fitness": primitives.fitness, "output": observe}

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
    ) -> Term:
        self.stats = Stats()
        target = refined_to_unrefined_type(type)
        if not isinstance(target, TypeConstructor) or target.name.name != "ControlProgram":
            raise UnsupportedSynthesisGoal("regus expects a ControlProgram hole; use a structure-synthesis problem")
        entry = metadata.get(fun_name, {})
        flags = minimize_flags_from_goals(entry.get("goals", []))
        if not flags or not entry.get("cluster") or output_value is None:
            raise UnsupportedSynthesisGoal(
                "regus needs numeric fitness decorators and @cluster with ControlObservation"
            )
        constructors: dict[str, Name] = {}
        for name, ty in ctx.vars():
            args = 0
            result = refined_to_unrefined_type(ty)
            while isinstance(result, AbstractionType):
                args += 1
                result = refined_to_unrefined_type(result.type)
            for kind, arity in {"halt": 0, "action": 1, "sequence": 2, "loop": 2, "branch": 3, "gap": 0}.items():
                if name.name == f"ControlProgram_{kind}" and result == target and args == arity:
                    constructors.setdefault(kind, name)
        if len(constructors) != 6:
            raise UnsupportedSynthesisGoal("regus requires the ControlProgram library constructors")
        # Earlier closed program definitions act as callable procedures in an
        # explicit curriculum. They are supplied by the problem, never guessed
        # from an environment/task name or copied from a reference solution.
        skills = tuple(
            Plan("skill", skill=name)
            for name, ty in ctx.concrete_vars()
            if refined_to_unrefined_type(ty) == target
            and name.name not in {fun_name.name, *(n.name for n in constructors.values())}
        )
        started = monotonic()
        front: list[ParetoEntry] = []
        protocol: tuple[int, int, int] | None = None

        def assess(plan: Plan):
            nonlocal front, protocol
            term = plan.term(constructors)
            self.stats.assessments += 1
            try:
                observation = decode(output_value(term))
            except ValueError as exc:
                if protocol is None:
                    raise UnsupportedSynthesisGoal(f"regus observation protocol: {exc}") from exc
                self.stats.invalid += 1
                return None
            shape = (observation.actions, observation.predicates, len(observation.episodes))
            if protocol is None:
                protocol = shape
            elif shape != protocol:
                raise UnsupportedSynthesisGoal("control vocabulary and seed count must be independent of the candidate")
            try:
                values = evaluate(term)
                quality = utility(values, flags)
            except (InvalidIndividualException, TimeoutInEvaluationException, ErrorInSynthesis, ValueError):
                self.stats.invalid += 1
                return None
            complete = not plan.contains("gap")
            # Prefix executions guide search, but may never be returned.
            valid = complete and observation.closed and validate(term)
            added = False
            if valid:
                self.stats.complete += 1
                front, added = update_pareto_front(front, values, term, flags)
            elapsed = monotonic() - started
            ui.register(term, values if valid else "Partial" if not complete else "Invalid", elapsed, added)
            ui.progress(self.stats.assessments, self.stats.assessments, elapsed)
            if added:
                ui.register_front(front, elapsed)
            return quality, observation

        # Probe the supplied protocol and retain a valid bounded baseline.
        baseline = assess(Plan("halt"))
        if baseline is None:
            raise SynthesisNotSuccessful("regus could not evaluate the problem's control observation")
        search(
            assess,
            baseline[1],
            seed=self.seed,
            budget=max(0.0, budget - (monotonic() - started)),
            config=self.config,
            stats=self.stats,
            skills=skills,
        )
        if not front:
            raise SynthesisNotSuccessful("regus found no complete, well-typed controller with finite fitness")
        return pick_pareto_member(front, self.seed)
