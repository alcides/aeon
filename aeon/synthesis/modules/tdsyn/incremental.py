"""Session-local, assumption-scoped SMT queries for related search branches."""

from __future__ import annotations

from contextlib import contextmanager
from copy import deepcopy
from dataclasses import dataclass, field
from typing import Iterator

import z3

from aeon.compilation.session import current_session
from aeon.core.liquid import LiquidLiteralBool, LiquidTerm, LiquidVar, liquid_free_vars
from aeon.core.types import AbstractionType, RefinedType, RefinementPolymorphism, Type, TypePolymorphism
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.verification.state import VerificationState


@dataclass
class ContextQueries:
    context: TypingContext
    snapshot: TypingContext = field(init=False)
    solver: z3.Solver = field(default_factory=z3.Solver)
    atoms: dict[tuple, z3.BoolRef] = field(default_factory=dict)
    declared_names: set[Name] = field(default_factory=set)
    active: bool = False

    def __post_init__(self) -> None:
        self.snapshot = deepcopy(self.context)
        for entry in self.context.entries:
            if hasattr(entry, "name"):
                self.declared_names.add(entry.name)
            ty = getattr(entry, "type", None)
            while isinstance(ty, (AbstractionType, TypePolymorphism, RefinementPolymorphism)):
                if isinstance(ty, AbstractionType):
                    self.declared_names.add(ty.var_name)
                    ty = ty.type
                else:
                    ty = ty.body

    def assumptions(self, bindings: dict[Name, Type], predicates: list[LiquidTerm]) -> list[z3.BoolRef]:
        from aeon.synthesis.modules.tdsyn.constraints import existential_formula, predicate_at

        bare = {name: ty.type if isinstance(ty, RefinedType) else ty for name, ty in bindings.items()}
        atoms = [predicate_at(ty, LiquidVar(name)) for name, ty in bindings.items()]
        atoms = list(dict.fromkeys(p for p in atoms + predicates if p != LiquidLiteralBool(True)))
        if not atoms:
            atoms = [LiquidLiteralBool(True)]
        # A long-running search must not retain every abandoned branch.
        if len(self.atoms) + len(atoms) > current_session().options.cache_limit:
            self.solver.reset()
            self.atoms.clear()
        result = []
        for atom in atoms:
            free = set(liquid_free_vars(atom))
            signature = tuple((n, ty) for n, ty in bare.items() if n in free)
            key = (atom, signature)
            selector = self.atoms.get(key)
            if selector is None:
                # Use the ordinary encoder for each obligation. Outer
                # refinements become separate atoms, so only newly introduced
                # obligations need translation on the next constructor step.
                formula = existential_formula(self.context, bare, [atom])
                selector = z3.FreshBool("tdsyn_branch")
                self.solver.add(z3.Implies(selector, formula))
                self.atoms[key] = selector
            result.append(selector)
        return result


@dataclass
class IncrementalState:
    generation: int = -1
    contexts: dict[int, ContextQueries] = field(default_factory=dict)


def clear_incremental_queries() -> None:
    current_session().state(IncrementalState).contexts.clear()


@contextmanager
def solver_query(
    ctx: TypingContext, bindings: dict[Name, Type], predicates: list[LiquidTerm]
) -> Iterator[tuple[z3.Solver, list[z3.BoolRef]]]:
    session = current_session()
    state = session.state(IncrementalState)
    generation = session.state(VerificationState).generation
    if state.generation != generation:
        state.contexts.clear()
        state.generation = generation
    query = state.contexts.get(id(ctx))
    if query is None or query.context is not ctx or ctx != query.snapshot:
        query = ContextQueries(ctx)
        state.contexts[id(ctx)] = query
        if len(state.contexts) > session.options.cache_limit:
            state.contexts.pop(next(iter(state.contexts)))
    if (
        query.active
        or any(n in query.declared_names for n in bindings)
        or any(isinstance(ty, (AbstractionType, TypePolymorphism, RefinementPolymorphism)) for ty in bindings.values())
    ):
        # Search witnesses normally have fresh names. For externally supplied
        # overlapping scopes, preserve the ordinary encoder's alpha-renaming
        # across the whole formula instead of renaming each atom separately.
        from aeon.synthesis.modules.tdsyn.constraints import existential_formula

        solver = z3.Solver()
        solver.add(existential_formula(ctx, bindings, predicates))
        yield solver, []
        return
    assumptions = query.assumptions(bindings, predicates)
    # Model-blocking clauses belong only to this enumeration, never siblings.
    query.solver.push()
    query.active = True
    try:
        yield query.solver, assumptions
    finally:
        query.solver.pop()
        query.active = False
        if len(query.atoms) > session.options.cache_limit:
            state.contexts.pop(id(ctx), None)
