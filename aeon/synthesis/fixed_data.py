"""Refinement-guided construction of fixed-size Boolean lists.

The checked nil/cons equations determine the spine. SMT checks scalar choices
against the original field and result contracts; objectives remain the search
backend's responsibility. Every emitted term still needs normal validation.
"""

from dataclasses import dataclass
from time import monotonic
from typing import Callable, Iterator

import z3

from aeon.core.liquid import LiquidVar
from aeon.core.terms import Literal, Term
from aeon.core.types import Type, t_bool
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.modules.cpsat_lists import ListExpansion, expand_list_schema
from aeon.synthesis.modules.tdsyn.constraints import predicate_at
from aeon.synthesis.modules.tdsyn.helpers import base_type_of
from aeon.synthesis.modules.tdsyn.incremental import solver_query
from aeon.synthesis.modules.tdsyn.worklist import substitute_holes_map
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name, fresh_counter
from aeon.verification.constructor_registry import get_constructor_groups
from aeon.verification.smt import make_variable


@dataclass
class FixedBooleanList:
    context: TypingContext
    expansion: ListExpansion
    deadline: float

    @classmethod
    def build(cls, ctx: TypingContext, goal: Type, skip: Callable[[Name], bool], deadline=float("inf")):
        base = base_type_of(goal)
        if base is None or base.name.name not in get_constructor_groups():
            return None
        names = get_constructor_groups()[base.name.name]
        constructors = [(n, ty) for n, ty in ctx.concrete_vars() if n.name in names and not skip(n)]
        try:
            expansion = expand_list_schema(Name("fixed", fresh_counter.fresh()), goal, constructors, ctx)
        except UnsupportedSynthesisGoal:
            return None
        if any(base_type_of(ty) != t_bool for ty in expansion.leaves.values()):
            return None
        assert expansion.result_name is not None
        expansion.constraints.append(predicate_at(goal, LiquidVar(expansion.result_name)))
        return cls(ctx, expansion, deadline)

    def _check(self, solver, assumptions):
        remaining = self.deadline - monotonic()
        if remaining <= 0:
            return z3.unknown
        solver.set(timeout=max(1, min(500, int(remaining * 1000))) if remaining != float("inf") else 500)
        return solver.check(*assumptions)

    def _term(self, values: list[bool]) -> Term:
        leaves: dict[Name, Term] = {name: Literal(value, t_bool) for name, value in zip(self.expansion.leaves, values)}
        return substitute_holes_map(self.expansion.template, leaves)

    def decode(self, genome: list[int], generation: int = 0) -> Term | None:
        """Let each codon prefer a Boolean; repair only infeasible choices.

        This keeps variation in every position instead of choosing between a
        small, fixed batch of solver models with a single codon.
        """
        if not genome or monotonic() >= self.deadline:
            return None
        expansion = self.expansion
        try:
            with solver_query(self.context, expansion.bindings, expansion.constraints) as (solver, assumptions):
                if self._check(solver, assumptions) != z3.sat:
                    return None
                choices: list[z3.BoolRef] = []
                for index, name in enumerate(expansion.leaves):
                    variable = make_variable(str(name), t_bool)
                    preferred = variable if genome[index % len(genome)] % 2 else z3.Not(variable)
                    answer = self._check(solver, assumptions + choices + [preferred])
                    if answer == z3.unknown:
                        return None
                    choices.append(preferred if answer == z3.sat else z3.Not(preferred))
                if self._check(solver, assumptions + choices) != z3.sat:
                    return None
                model = solver.model()
                return self._term(
                    [
                        z3.is_true(model.eval(make_variable(str(n), t_bool), model_completion=True))
                        for n in expansion.leaves
                    ]
                )
        except (AssertionError, KeyError, TypeError, ValueError, NotImplementedError, z3.Z3Exception):
            return None

    def candidates(self) -> Iterator[Term]:
        """Enumerate feasible Boolean assignments without optimizing their score."""
        if monotonic() >= self.deadline:
            return
        expansion = self.expansion
        try:
            with solver_query(self.context, expansion.bindings, expansion.constraints) as (solver, assumptions):
                variables = [make_variable(str(n), t_bool) for n in expansion.leaves]
                while self._check(solver, assumptions) == z3.sat:
                    model = solver.model()
                    values = [z3.is_true(model.eval(v, model_completion=True)) for v in variables]
                    yield self._term(values)
                    if not variables:
                        return
                    solver.add(z3.Or(*[v != value for v, value in zip(variables, values)]))
        except (AssertionError, KeyError, TypeError, ValueError, NotImplementedError, z3.Z3Exception):
            return
