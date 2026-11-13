"""Shared validation and objective evaluation for complete-program candidates.

Solvers and source-level learners have different candidate generators, but
their substitutions, contracts, fixed property corpora and resource objectives
must have the same meaning as ordinary expression synthesis.
"""

from __future__ import annotations

from collections.abc import Mapping

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Term
from aeon.core.types import top
from aeon.decorators.api import Metadata
from aeon.synthesis.api import InvalidIndividualException, TimeoutInEvaluationException
from aeon.synthesis.bounded_cnf import check_program
from aeon.synthesis.constructors import prepare_candidate
from aeon.synthesis.decorators import Goal
from aeon.synthesis.evaluation_pool import EvaluationPool, OK, TIMEOUT
from aeon.synthesis.fitness_eval import (
    CandidateEvaluationCache,
    make_bundled_fitness_evaluator,
    without_main_placeholder,
)
from aeon.synthesis.identification import get_holes, term_has_holes
from aeon.synthesis.joint import JointCandidate
from aeon.synthesis.modules.tdsyn.worklist import substitute_holes_map
from aeon.synthesis.pbt.runner import make_property_fitness, property_corpora_for_targets
from aeon.typechecking.context import TypingContext
from aeon.typechecking.linearity import check_linearity
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


class ProgramSpecifications:
    """Adapt specification decorators to complete-program acceptance and scores.

    ``hard_kinds`` decides which loss goals are acceptance conditions. A noisy
    learner leaves examples/CSV soft; a satisfaction solver checks them exactly.
    Properties use one deterministic corpus and can likewise be hard or soft.
    ``pooled=False`` is for backends already running in a killable worker: it
    deliberately avoids creating child processes inside daemon workers.
    """

    def __init__(
        self,
        ctx: TypingContext,
        ectx: EvaluationContext,
        program: Term,
        targets: list[tuple[Name, list[Name]]],
        metadata: Metadata,
        *,
        hard_kinds: frozenset[str] = frozenset({"example", "constraint"}),
        properties_hard: bool = True,
        omit_objectives: frozenset[str] = frozenset(),
        budget_eval: float = 1.0,
        constructor_names: set[str] | None = None,
        pooled: bool = True,
    ):
        self.ctx = ctx
        self.program = without_main_placeholder(program)
        self.source_metadata = metadata
        self.holes = tuple(dict.fromkeys(hole for _, holes in targets for hole in holes))
        if not self.holes or set(self.holes) != set(get_holes(self.program)):
            raise InvalidIndividualException("complete-program specifications need every open hole")
        names = {function for function, _ in targets}
        anchor = targets[0][0]
        workers_ctx = EvaluationContext(
            ectx.variables,
            metadata=ectx.metadata,
            pipeline=None,
            trace=ectx.trace,
            trace_stack=ectx.trace_stack,
            reject_holes=True,
        )
        corpora = property_corpora_for_targets(
            ctx,
            self.program,
            metadata,
            names,
            names,
            constructor_names=constructor_names,
            evaluation_ctx=ectx,
        )
        property_goals = [Goal(True, 1, corpus.spec.name, "property") for corpus in corpora]
        property_evaluators = {
            corpus.spec.name: make_property_fitness(corpus, workers_ctx, target=anchor) for corpus in corpora
        }
        self.all_goals: list[Goal] = list(
            dict.fromkeys(goal for entry in metadata.values() for goal in entry.get("goals", []))
        )
        self.all_goals.extend(goal for goal in property_goals if goal not in self.all_goals)
        self.goals = [goal for goal in self.all_goals if goal.kind not in omit_objectives]
        self.checks = [
            goal
            for goal in self.all_goals
            if goal.kind == "require" or goal.kind in hard_kinds or (properties_hard and goal.kind == "property")
        ]
        self.name = Name("$program", 0)
        self.metadata = dict(metadata) | {self.name: {"goals": self.goals}}

        runtime_cache = CandidateEvaluationCache() if any(g.kind == "require" for g in self.all_goals) else None

        def evaluator(goals):
            properties = [property_evaluators[goal.function] for goal in goals if goal.kind == "property"]
            return make_bundled_fitness_evaluator(
                goals, workers_ctx, anchor, self.program, properties, runtime_cache=runtime_cache
            )

        self._fitness = evaluator(self.goals)
        self._checks = evaluator(self.checks)
        # Fitness already includes most hard constraints. Reuse their exact
        # vector positions in the same worker task instead of interpreting the
        # whole candidate twice within one evaluation timeout.
        goal_indices = {}
        offset = 0
        for goal in self.goals:
            goal_indices[goal] = range(offset, offset + goal.length)
            offset += goal.length
        check_indices = (
            [index for goal in self.checks for index in goal_indices[goal]]
            if all(goal in goal_indices for goal in self.checks)
            else None
        )
        cached_program: Term | None = None
        cached_scores: list[float] = []

        def fitness(program):
            nonlocal cached_program, cached_scores
            cached_program = None
            cached_scores = self._fitness(program)
            cached_program = program
            return cached_scores

        def checks(program):
            if program is cached_program and check_indices is not None:
                return [cached_scores[index] for index in check_indices]
            # Omitted objectives and a failed fitness computation must not
            # suppress independent hard-constraint evaluation.
            return self._checks(program)

        self.pool = (
            EvaluationPool(
                self.replace,
                {"fitness": fitness, "specification": checks},
                budget_eval=budget_eval,
            )
            if pooled
            else None
        )
        self._last_candidate: Term | None = None
        self._last_results: dict = {}

    def _results(self, candidate: Term) -> dict:
        assert self.pool is not None
        if candidate != self._last_candidate:
            self._last_results = self.pool.run(candidate)
            self._last_candidate = candidate
        return self._last_results

    def candidate(self, mapping: Mapping[Name, Term | None]) -> JointCandidate:
        terms = tuple(mapping.get(hole) for hole in self.holes)
        if any(term is None for term in terms):
            raise InvalidIndividualException("candidate does not fill every program hole")
        return JointCandidate(tuple(term for term in terms if term is not None))

    def mapping(self, candidate: Term | None) -> dict[Name, Term | None]:
        if candidate is None:
            return dict.fromkeys(self.holes)
        if not isinstance(candidate, JointCandidate) or len(candidate.terms) != len(self.holes):
            raise InvalidIndividualException("candidate has the wrong hole count")
        return dict(zip(self.holes, candidate.terms))

    def replace(self, candidate: Term) -> Term:
        if not isinstance(candidate, JointCandidate) or len(candidate.terms) != len(self.holes):
            raise InvalidIndividualException("candidate has the wrong hole count")
        for value in candidate.terms:
            if term_has_holes(value):
                raise InvalidIndividualException("candidate contains an unresolved hole")
        program = substitute_holes_map(self.program, dict(zip(self.holes, candidate.terms)))
        if term_has_holes(program):
            raise InvalidIndividualException("candidate leaves an unresolved hole")
        return program

    def validate(self, candidate: Term) -> bool:
        try:
            program = self.replace(candidate)
            if check_linearity(program, self.ctx):
                return False
            if not check_program(program, self.source_metadata):
                return False
            prepared = prepare_candidate(candidate)
            checking_program = self.replace(prepared) if prepared is not candidate else program
            if not check_type(self.ctx, checking_program, top):
                return False
            if not self.checks:
                return True
            if self.pool is None:
                scores = self._checks(program)
            else:
                status, scores = self._results(candidate).get("specification", ("error", None))
                if status != OK or not isinstance(scores, list):
                    return False
            return all(score == 0 for score in scores)
        except (InvalidIndividualException, TimeoutInEvaluationException):
            return False

    def evaluate(self, candidate: Term) -> list[float]:
        if any(g.kind == "require" for g in self.all_goals) and not self.validate(candidate):
            raise InvalidIndividualException("candidate violates its type or @require")
        if self.pool is None:
            return self._fitness(self.replace(candidate))
        status, scores = self._results(candidate).get("fitness", ("error", None))
        if status == TIMEOUT:
            raise TimeoutInEvaluationException()
        if status != OK or not isinstance(scores, list):
            raise InvalidIndividualException("candidate has no objective value")
        return scores

    def close(self) -> None:
        if self.pool is not None:
            self.pool.close()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()
