from __future__ import annotations

import random
from itertools import chain, count
from heapq import heappop, heappush
from collections import OrderedDict, deque
from collections.abc import Iterator
from dataclasses import dataclass, replace
from time import monotonic_ns
from typing import Callable

from loguru import logger

from aeon.compilation.session import current_session
from aeon.core.terms import Abstraction, Annotation, Application, Hole, Term, Var
from aeon.core.types import AbstractionType, RefinedType, Type, type_free_term_vars
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.evaluation_pool import inconclusive_evaluations
from aeon.synthesis.budgets import EvaluationWatchdogExpired
from aeon.synthesis.identification import get_holes
from aeon.synthesis.modules.tdsyn.actions import (
    backward_abs_candidates,
    backward_app_candidates,
    backward_candidates,
    backward_close_candidates,
    backward_if_candidates,
    backward_lit_candidates,
    forward_candidates,
    forward_close_candidates,
    forward_let_abs_candidates,
    forward_let_app_candidates,
    forward_let_if_candidates,
    forward_let_tabs_candidates,
    forward_let_tapp_candidates,
    iter_backward_candidates,
    iter_forward_candidates,
)
from aeon.synthesis.modules.tdsyn.helpers import (
    bind_constructor_arguments,
    clear_tdsyn_caches,
    make_skip_fn,
    is_constructor_term,
    is_eliminator_term,
)
from aeon.synthesis.modules.tdsyn.constraints import deadline, has_refinement
from aeon.synthesis.modules.tdsyn.smt_solve import all_leaf_holes, solve_literals
from aeon.synthesis.modules.tdsyn.bindings import open_abstraction
from aeon.synthesis.modules.tdsyn.worklist import (
    Child,
    PartialAST,
    TypedHole,
    expand_at_hole,
    fresh_hole,
    locate_holes,
    substitute_hole,
    substitute_holes_map,
    term_at,
)
from aeon.synthesis.qtt import QTTValidator
from aeon.synthesis.typecheck_cache import _typed_key
from aeon.synthesis.pareto import ParetoEntry, minimize_flags_from_goals, pick_pareto_member, update_pareto_front
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.linearity import check_linearity
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name
from aeon.verification.state import VerificationState

_loc = SynthesizedLocation("tdsyn")


@dataclass
class PendingExpansion:
    partial: PartialAST
    hole: TypedHole
    children: Iterator[PartialAST]


def _get_elapsed_time(start_time: int) -> float:
    return (monotonic_ns() - start_time) * 0.000000001


def _is_arrow(ty: Type) -> bool:
    while isinstance(ty, RefinedType):
        ty = ty.type
    return isinstance(ty, AbstractionType)


def _bound_eliminator(term: Term, goal: Type) -> bool:
    """Prioritize a match on a concrete input mentioned by the goal contract."""
    arguments = []
    while isinstance(term, Application):
        arguments.append(term.arg)
        term = term.fun
    return (
        bool(arguments)
        and isinstance(arguments[-1], Var)
        and arguments[-1].name in type_free_term_vars(goal)
        and is_eliminator_term(term)
    )


def _select_hole(holes: list[TypedHole]) -> TypedHole:
    """Pick the next hole.

    Function holes have a single abstraction production, so they come before
    a datatype sibling. Otherwise the last structural hole is the handler
    body of a recursor, which has to be built before the nil branch is guessed.
    """
    structural = [hole for hole in holes if not all_leaf_holes([hole])]
    if not structural:
        return holes[0]
    functions = [hole for hole in structural if _is_arrow(hole.expected_type)]
    if functions:
        return functions[0]
    return structural[-1]


def _peel_abstractions(ty: Type, ctx: TypingContext) -> tuple[Term, Type, TypingContext, list[TypedHole]]:
    """If the target type is a function type, peel off abstractions.

    Returns (wrapper_term_with_hole, inner_type, extended_ctx, [inner_hole]).
    For non-function types, returns a single hole.
    """
    if not isinstance(ty, AbstractionType):
        hole_term, typed_hole = fresh_hole(ty, ctx, path=())
        return hole_term, ty, ctx, [typed_hole]

    current_type: Type = ty
    current_ctx = ctx
    var_names: list[Name] = []

    while isinstance(current_type, AbstractionType):
        name, current_type, current_ctx = open_abstraction(current_type, current_ctx)
        var_names.append(name)

    hole_path = tuple(Child.BODY for _ in var_names)
    inner_hole_term, inner_typed_hole = fresh_hole(current_type, current_ctx, path=hole_path)

    term: Term = inner_hole_term
    for var_name in reversed(var_names):
        term = Abstraction(var_name, term, _loc)

    return term, current_type, current_ctx, [inner_typed_hole]


class TDSynSynthesizer(Synthesizer):
    """Type-directed synthesizer using backward and forward actions with SMT-based subtyping.

    Supports enumerative (BFS) and random exploration, with both directions
    or backward-only expansion. All variants share validation and objectives.
    Loops until the time budget is exhausted, restarting with shuffled expansion
    order on each iteration to explore different term structures.

    Completed assessments are deduplicated within each search by default.
    ``deduplicate=False`` disables this bounded cache for comparisons; skipping
    validation can also change the subsequent SMT search trajectory.
    """

    supports_size_objective = True
    supports_deterministic_budget = True

    def __init__(
        self,
        mode: str = "enumerative",
        seed: int = 0,
        *,
        direction: str = "both",
        expansion: str = "eager",
        deduplicate: bool = True,
        dedup_capacity: int = 4096,
    ):
        assert mode in ("enumerative", "random")
        assert direction in ("both", "backward")
        if expansion not in ("eager", "lazy"):
            raise ValueError(f"Unknown TDSyn expansion mode: {expansion}")
        if dedup_capacity < 1:
            raise ValueError("candidate deduplication capacity must be positive")
        self.mode = mode
        self.direction = direction
        self.expansion = expansion
        self.seed = seed
        self._rng = random.Random(seed)
        self._iteration = 0
        self._recursive_guidance = False
        self.deduplicate = deduplicate
        self.dedup_capacity = dedup_capacity
        self._completed: OrderedDict[tuple, None] = OrderedDict()
        self.duplicates_skipped = 0
        self.dedup_bypassed = 0

    def prepare_context(self, ctx, program, fun_name, metadata):
        """Weaken a ``decreasing_by`` hypothesis and allow the recursive name.

        Identification installs the full declared type, and ``should_skip``
        drops ``fun_name`` unless ``metadata[fun_name]["recursion"]`` is set.
        ``@allow_recursion`` is the only other writer of that flag. A metric
        has to do both jobs: replace the binding with ``recursive_context``
        and open the skip, or the weakened hypothesis is never a component.
        """
        from aeon.synthesis.identification import iterate_top_level

        owner = next((node for node in iterate_top_level(program) if node.var_name == fun_name), None)
        self._recursive_guidance = bool(owner is not None and owner.decreasing_by)
        if owner is None or not owner.decreasing_by:
            return ctx
        entry = metadata.get(fun_name)
        if not isinstance(entry, dict):
            entry = {}
            metadata[fun_name] = entry
        entry["recursion"] = True
        from aeon.synthesis.modules.synquid.functions import recursive_context

        return recursive_context(ctx, program, fun_name)

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
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        # Retain completed assessments through restarts, never across problems.
        self._completed.clear()
        self.duplicates_skipped = 0
        self.dedup_bypassed = 0
        if self.deterministic_budget is not None:
            self._rng = random.Random(self.seed)
            self._iteration = 0

        skip = make_skip_fn(fun_name, metadata)
        goals = metadata.get(fun_name, {}).get("goals", [])
        self._has_goals = bool(goals)
        self._minimize = minimize_flags_from_goals(goals)
        start_time = monotonic_ns()
        front: list[ParetoEntry] = []
        ui.register(None, None, 0, True)
        clear_tdsyn_caches()

        # Peel abstractions from the target type
        initial_term, inner_type, inner_ctx, initial_holes = _peel_abstractions(type, ctx)

        initial_partial = PartialAST(
            term=initial_term,
            holes=initial_holes,
            depth=0,
            expected_type=type,
            context=ctx,
            check_sketch=validate.feasible if isinstance(validate, QTTValidator) else None,
        )

        token = deadline.set(start_time * 1e-9 + budget)
        try:
            # Loop: restart search when worklist/walk is exhausted, until budget runs out
            while _get_elapsed_time(start_time) < budget:
                if self.mode == "enumerative":
                    front, early = self._enumerative_search(
                        initial_partial, skip, validate, evaluate, start_time, budget, ui, front
                    )
                else:
                    front, early = self._random_search(
                        initial_partial, skip, validate, evaluate, start_time, budget, ui, front
                    )
                # If no goals, return the first valid term found
                if early is not None:
                    return early

            if front:
                ui.register_front(front, _get_elapsed_time(start_time))
                return pick_pareto_member(front, self.seed)
            raise SynthesisNotSuccessful("TDSynSynthesizer: no valid candidate found within budget")
        finally:
            deadline.reset(token)

    def _remember_complete(self, key: tuple | None) -> None:
        if key is not None:
            self._completed[key] = None
            if len(self._completed) > self.dedup_capacity:
                self._completed.popitem(last=False)

    def _try_complete(
        self,
        partial: PartialAST,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        ui: SynthesisUI,
        front: list[ParetoEntry],
    ) -> tuple[list[ParetoEntry], Term | None]:
        """Try to validate and evaluate a complete term.

        Returns ``(front, early)`` where ``early`` is a no-objective solution
        that should stop the search immediately.
        """
        if not partial.is_complete():
            return front, None
        key = None
        if self.deduplicate:
            try:
                # Snapshot before constructor preparation allocates fresh names.
                # Term equality erases annotations and conflates Boolean/int values.
                key = _typed_key(partial.term)
            except (TypeError, RecursionError):
                self.dedup_bypassed += 1
            if key is not None and key in self._completed:
                self._completed.move_to_end(key)
                self.duplicates_skipped += 1
                return front, None
        if not partial.qtt_feasible():
            self._remember_complete(key)
            return front, None
        term = bind_constructor_arguments(partial.term)
        if term is not partial.term and not replace(partial, term=term).qtt_feasible():
            self._remember_complete(key)
            return front, None
        state = current_session().state(VerificationState)
        uncertain_before = state.inconclusive_queries, inconclusive_evaluations.get()
        try:
            if validate(term):
                if not self._has_goals:
                    ui.register(term, [], _get_elapsed_time(start_time), True)
                    return front, term
                score = evaluate(term)
                front, is_best = update_pareto_front(front, score, term, self._minimize)
                self.pareto_front = front
                elapsed = _get_elapsed_time(start_time)
                if is_best:
                    ui.register_front(front, elapsed)
                ui.register(term, score, elapsed, is_best)
            else:
                ui.register(term, "Invalid", _get_elapsed_time(start_time), False)
        except EvaluationWatchdogExpired:
            raise
        except Exception:
            ui.register(term, "Invalid", _get_elapsed_time(start_time), False)
            return front, None
        # Retry uncertainty and worker failures; remember both successful scores
        # and definitive type/runtime rejections for this synthesis problem.
        if uncertain_before == (state.inconclusive_queries, inconclusive_evaluations.get()):
            self._remember_complete(key)
        return front, None

    def _try_smt_complete(
        self,
        partial: PartialAST,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        ui: SynthesisUI,
        front: list[ParetoEntry],
    ) -> tuple[list[ParetoEntry], Term | None, bool]:
        """Try to complete a partial AST by solving all remaining holes with SMT.

        Returns ``(front, early, smt_succeeded)``. ``smt_succeeded`` is True if
        SMT produced at least one solution attempt (even if validation failed).
        """
        if not partial.holes or not all_leaf_holes(partial.holes):
            return front, None, False

        solutions = solve_literals(partial.holes)
        if not solutions:
            return front, None, False

        early: Term | None = None
        for solution in solutions:
            if monotonic_ns() * 1e-9 >= deadline.get():
                break
            term = substitute_holes_map(partial.term, solution)
            complete = replace(partial, term=term, holes=[])
            front, early = self._try_complete(complete, validate, evaluate, start_time, ui, front)
            if early is not None:
                return front, early, True

        return front, None, True

    def _expand_hole(
        self,
        partial: PartialAST,
        hole: TypedHole,
        skip: Callable[[Name], bool],
        max_depth: int | None = None,
    ) -> list[PartialAST]:
        """Expand a hole using the selected directions and the shared worklist."""
        results: list[PartialAST] = []
        actions = [backward_candidates]
        if self.direction == "both":
            actions.append(forward_candidates)

        for action_fn in actions:
            try:
                candidates = action_fn(hole, skip)
            except Exception as e:
                logger.debug(f"tdsyn: action failed: {e}")
                continue

            for replacement, new_holes in candidates:
                new_depth = partial.depth + (1 if new_holes else 0)
                if max_depth is None or new_depth <= max_depth:
                    expanded = expand_at_hole(partial, hole, replacement, new_holes, new_depth)
                    if expanded.qtt_feasible():
                        results.append(expanded)

        matching_input = partial.depth == 0 and any(
            _bound_eliminator(term_at(result.term, hole.path), hole.expected_type) for result in results
        )
        if not self._recursive_guidance and not matching_input:
            if self._iteration > 0 and results:
                self._rng.shuffle(results)
            return results

        # A depth-0 refined eliminator is the match. Keep it ahead of the
        # shuffle, and keep nested eliminators behind variable closes so a
        # case arm is not another copy of T_rec.
        guided: list[PartialAST] = []
        folds: list[PartialAST] = []
        values: list[PartialAST] = []
        ordinary: list[PartialAST] = []
        nested_elims: list[PartialAST] = []
        for expanded in results:
            placed = term_at(expanded.term, hole.path)
            if _bound_eliminator(placed, hole.expected_type) and partial.depth == 0:
                guided.append(expanded)
            elif is_eliminator_term(placed):
                nested_elims.append(expanded)
            elif is_constructor_term(placed) and not locate_holes(placed):
                # ``cons h (recursive t ys)`` is a finished case arm. Keep it
                # ahead of the shuffle so the nil branch is tried next.
                folds.append(expanded)
            elif not locate_holes(placed):
                values.append(expanded)
            else:
                ordinary.append(expanded)
        if self._iteration > 0 and ordinary:
            self._rng.shuffle(ordinary)
        if self._iteration > 0 and nested_elims:
            self._rng.shuffle(nested_elims)
        return guided + folds + values + ordinary + nested_elims

    def _iter_expansions(
        self,
        partial: PartialAST,
        hole: TypedHole,
        skip: Callable[[Name], bool],
        max_depth: int | None = None,
        *,
        rng: random.Random | None = None,
        constructors_only: bool = False,
    ) -> Iterator[PartialAST]:
        """Construct and check one production at a time, on consumer demand."""
        actions = [iter_backward_candidates(hole, skip, rng, constructors_only=constructors_only)]
        if self.direction == "both" and not constructors_only:
            actions.append(iter_forward_candidates(hole, skip, rng))
        for candidates in actions:
            try:
                while monotonic_ns() * 1e-9 < deadline.get():
                    candidate = next(candidates, None)
                    if candidate is None:
                        break
                    replacement, new_holes = candidate
                    new_depth = partial.depth + (1 if new_holes else 0)
                    if max_depth is None or new_depth <= max_depth:
                        expanded = expand_at_hole(partial, hole, replacement, new_holes, new_depth)
                        if expanded.qtt_feasible():
                            yield expanded
            except Exception as error:
                logger.debug(f"tdsyn: lazy action failed: {error}")

    def _walk_expansions(self, partial, hole, skip, rng, max_depth=None):
        """Try randomized constructor productions first on most lazy walks.

        Randomize production descriptions before their feasibility checks.
        The consumer stops at the first usable child, without scanning all
        siblings as the eager random walk does.
        """
        if rng.random() < 0.9:
            yield from self._iter_expansions(partial, hole, skip, max_depth, rng=rng, constructors_only=True)
        yield from self._iter_expansions(partial, hole, skip, max_depth, rng=rng)

    def iter_input_candidates(
        self,
        ctx: TypingContext,
        target: Type,
        skip: Callable[[Name], bool],
        max_depth: int,
        max_expansions: int = 4096,
        max_worklist: int = 4096,
        initial: PartialAST | None = None,
    ) -> Iterator[Term | None]:
        """Bounded, resumable input search using this backend's expansions.

        Unlike ``synthesize``, keep yielding candidates rather than stopping at
        the first answer. ``None`` denotes a failed random walk. Validation is
        deliberately left to PBT's common typechecking gate.
        """
        if initial is None:
            term, _, _, holes = _peel_abstractions(target, ctx)
            initial = PartialAST(term, holes, 0, expected_type=target, context=ctx)
        else:
            initial = replace(initial, expected_type=target, context=ctx)
        if not initial.qtt_feasible():
            return

        def completions(partial: PartialAST) -> list[Term]:
            if not partial.holes or not all_leaf_holes(partial.holes):
                return []
            terms = [substitute_holes_map(partial.term, solution) for solution in solve_literals(partial.holes)]
            return [term for term in terms if replace(partial, term=term, holes=[]).qtt_feasible()]

        if self.mode == "random":
            for _ in range(max_expansions):
                partial = replace(initial, holes=list(initial.holes), depth=0)
                for _step in range(max_depth * 2):
                    if partial.is_complete():
                        break
                    solved = completions(partial)
                    if solved:
                        partial = replace(partial, term=self._rng.choice(solved), holes=[])
                        break
                    hole = self._rng.choice(partial.holes)
                    if self.expansion == "lazy":
                        selected = next(self._walk_expansions(partial, hole, skip, self._rng, max_depth), None)
                        if selected is None:
                            break
                        partial = selected
                    else:
                        options = self._expand_hole(partial, hole, skip, max_depth)
                        if not options:
                            break
                        partial = self._rng.choice(options)
                yield partial.term if partial.is_complete() and partial.qtt_feasible() else None
            return

        worklist = deque([initial])
        seen: set[Term] = set()
        for _ in range(max_expansions):
            if not worklist:
                return
            partial = worklist.popleft()
            candidates = [partial.term] if partial.is_complete() else completions(partial)
            for candidate in candidates:
                if candidate not in seen:
                    seen.add(candidate)
                    yield candidate
            if partial.is_complete():
                continue
            expansions = (
                self._iter_expansions(partial, partial.holes[0], skip, max_depth)
                if self.expansion == "lazy"
                else iter(self._expand_hole(partial, partial.holes[0], skip, max_depth))
            )
            for expanded in expansions:
                complete = [expanded.term] if expanded.is_complete() else completions(expanded)
                for candidate in complete:
                    if candidate not in seen:
                        seen.add(candidate)
                        yield candidate
                if not expanded.is_complete() and not complete:
                    worklist.append(expanded)
                    if len(worklist) > max_worklist:
                        return

    def _enumerative_search(
        self,
        initial: PartialAST,
        skip: Callable[[Name], bool],
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        budget: float,
        ui: SynthesisUI,
        front: list[ParetoEntry],
    ) -> tuple[list[ParetoEntry], Term | None]:
        """Fair BFS with a constructor lane for refinement-guided data building.

        Alternate ordinary BFS with constructor continuations. This reaches
        deep data without enumerating every unrelated shallow function first,
        while keeping those other expressions in the search. Neither lane has
        a depth or candidate-count cutoff.
        """
        self._iteration += 1
        tickets = count()
        worklist: deque[tuple[int, PartialAST | PendingExpansion, bool]] = deque([(next(tickets), initial, True)])
        constructors: list[tuple[int, int, PartialAST]] = []
        # Siblings of a depth-0 eliminator wait until that match is exhausted.
        # The worklist would otherwise resume them before the match's body.
        suspended: deque[tuple[int, PendingExpansion]] = deque()
        visited: set[int] = set()
        guided_turn = False
        work: PartialAST | PendingExpansion

        while worklist or constructors or suspended:
            if _get_elapsed_time(start_time) > budget:
                break

            if not worklist and not constructors:
                ticket_s, pending_s = suspended.popleft()
                worklist.append((ticket_s, pending_s, False))
                continue

            if constructors and (guided_turn or not worklist):
                _, ticket, work = heappop(constructors)
                constructive = True
            else:
                ticket, work, constructive = worklist.popleft()
            guided_turn = not guided_turn
            if ticket in visited:
                continue
            visited.add(ticket)

            if isinstance(work, PendingExpansion):
                partial, hole, expanded = work.partial, work.hole, work.children
            else:
                partial = work
                if partial.is_complete():
                    front, early = self._try_complete(partial, validate, evaluate, start_time, ui, front)
                    if early is not None:
                        return front, early
                    continue

                # Try SMT completion if all holes are leaf-solvable.
                front, early, _ = self._try_smt_complete(partial, validate, evaluate, start_time, ui, front)
                if early is not None:
                    return front, early

                # Leave scalar payloads for joint SMT completion. A function hole
                # has one production, so open it before a datatype sibling. The
                # remaining structural hole is the last one: a recursor's
                # handler body, not its nil branch.
                hole = _select_hole(partial.holes)
                expanded = (
                    self._iter_expansions(partial, hole, skip)
                    if self.expansion == "lazy"
                    else iter(self._expand_hole(partial, hole, skip))
                )

            saw_value = False
            for new_partial in expanded:
                if _get_elapsed_time(start_time) > budget:
                    break
                if self.expansion == "lazy":
                    # Resume siblings through the ordinary queue. A constructor
                    # child can progress immediately through the guided lane;
                    # postponed alternatives still receive fair FIFO turns.
                    worklist.append((next(tickets), PendingExpansion(partial, hole, expanded), constructive))
                guide_eliminator = False
                if new_partial.is_complete():
                    saw_value = True
                    front, early = self._try_complete(new_partial, validate, evaluate, start_time, ui, front)
                    if early is not None:
                        return front, early
                else:
                    # Try SMT on newly expanded partials too
                    front, early, _ = self._try_smt_complete(new_partial, validate, evaluate, start_time, ui, front)
                    if early is not None:
                        return front, early
                    placed = term_at(new_partial.term, hole.path)
                    opens = bool(locate_holes(placed))
                    # A refined goal's eliminator is the match. Give it the
                    # constructor lane and do not spend the budget proving
                    # every preceding prelude operator first.
                    guide_eliminator = (
                        partial.depth == 0
                        and has_refinement(hole.expected_type)
                        and _bound_eliminator(placed, hole.expected_type)
                    )
                    # Finished arms (the fold, then variables) are validated
                    # before a nested eliminator or a three-hole if is built.
                    if (
                        self._recursive_guidance
                        and self.expansion != "lazy"
                        and not guide_eliminator
                        and partial.depth > 0
                        and saw_value
                        and opens
                    ):
                        suspended.append(
                            (next(tickets), PendingExpansion(partial, hole, chain((new_partial,), expanded)))
                        )
                        break
                    if not opens:
                        saw_value = True
                    follows_constructors = constructive and (is_constructor_term(placed) or guide_eliminator)
                    if guide_eliminator and self.expansion != "lazy":
                        suspended.append((next(tickets), PendingExpansion(partial, hole, expanded)))
                    ticket = next(tickets)
                    worklist.append((ticket, new_partial, follows_constructors))
                    if follows_constructors:
                        heappush(constructors, (-new_partial.depth, ticket, new_partial))
                if self.expansion == "lazy" or guide_eliminator:
                    break

        return front, None

    def _random_search(
        self,
        initial: PartialAST,
        skip: Callable[[Name], bool],
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        budget: float,
        ui: SynthesisUI,
        front: list[ParetoEntry],
    ) -> tuple[list[ParetoEntry], Term | None]:
        """Random exploration search."""
        rng = random.Random(self.seed)

        while _get_elapsed_time(start_time) < budget:
            # Start fresh from initial each time for random search
            partial = replace(initial, holes=list(initial.holes))

            # Probabilistic restarts have no maximum walk length. Every finite
            # constructor depth remains reachable, while bad walks do not
            # monopolize the entire budget.
            steps = 0
            while not partial.is_complete():
                if _get_elapsed_time(start_time) > budget:
                    break

                # Try SMT completion first
                front, early, _ = self._try_smt_complete(partial, validate, evaluate, start_time, ui, front)
                if early is not None:
                    return front, early

                # Pick a random hole
                structural = [h for h in partial.holes if not all_leaf_holes([h])]
                hole = rng.choice(structural or partial.holes)

                if self.expansion == "lazy":
                    selected = None
                    for candidate in self._walk_expansions(partial, hole, skip, rng):
                        if _get_elapsed_time(start_time) >= budget:
                            break
                        front, early = self._try_complete(candidate, validate, evaluate, start_time, ui, front)
                        if early is None:
                            front, early, _ = self._try_smt_complete(
                                candidate, validate, evaluate, start_time, ui, front
                            )
                        if early is not None:
                            return front, early
                        selected = candidate
                        break
                    # A complete (possibly rejected) proposal ends this walk.
                    # Do not enumerate its siblings or grow another expression
                    # inside the same failed structure before restarting.
                    if selected is None or selected.is_complete() or (steps and rng.random() < 1 / (steps + 2)):
                        break
                    partial = selected
                    steps += 1
                    continue

                # Get all candidates from the selected directions.
                all_candidates: list[PartialAST] = self._expand_hole(partial, hole, skip)

                if not all_candidates:
                    break

                # Check completions before walking deeper (in particular nil
                # at the required tail length). Rejected SMT proposals do not
                # suppress ordinary expansions of their holes.
                for candidate in all_candidates:
                    if _get_elapsed_time(start_time) >= budget:
                        break
                    front, early = self._try_complete(candidate, validate, evaluate, start_time, ui, front)
                    if early is None:
                        front, early, _ = self._try_smt_complete(candidate, validate, evaluate, start_time, ui, front)
                    if early is not None:
                        return front, early
                if steps and rng.random() < 1 / (steps + 2):
                    break
                constructors = [p for p in all_candidates if is_constructor_term(term_at(p.term, hole.path))]
                choices = constructors if constructors and rng.random() < 0.9 else all_candidates
                partial = rng.choice(choices)
                steps += 1

            if partial.is_complete():
                front, early = self._try_complete(partial, validate, evaluate, start_time, ui, front)
                if early is not None:
                    return front, early

        return front, None


def _rename_subgoals(term: Term, fun_name: Name) -> Term:
    """Give the remaining holes of a partial result unique, readable names.

    Fresh tdsyn holes all share the display name ``tdsyn_hole`` (they differ
    only in their internal counter), so a partial term printed back into the
    source would contain several indistinguishable ``?tdsyn_hole`` holes.
    """
    renamed = term
    for i, hole_name in enumerate(get_holes(renamed), start=1):
        renamed = substitute_hole(renamed, hole_name, Hole(Name(f"{fun_name.name}_goal_{i}", 0), _loc))
    return renamed


# The candidate-generating action behind each one-step tactic backend.
# ``backward`` decomposes the goal type with all backward constructions
# combined; the granular ``backward_*`` tactics each apply exactly one of them
# (abstraction, literal, close with a variable, application, if-then-else).
# The ``forward_*`` tactics either close the goal with a variable of the
# goal's type (``forward_close``) or grow the scope with a
# ``let v := <value> in ?goal`` binding whose value is one term former
# (application, if-then-else, type application, abstraction, or type
# abstraction).
ONE_STEP_ACTIONS: dict[str, Callable] = {
    "backward": backward_candidates,
    "backward_abs": backward_abs_candidates,
    "backward_lit": backward_lit_candidates,
    "backward_close": backward_close_candidates,
    "backward_app": backward_app_candidates,
    "backward_if": backward_if_candidates,
    "forward_close": forward_close_candidates,
    "forward_let_app": forward_let_app_candidates,
    "forward_let_if": forward_let_if_candidates,
    "forward_let_tapp": forward_let_tapp_candidates,
    "forward_let_abs": forward_let_abs_candidates,
    "forward_let_tabs": forward_let_tabs_candidates,
}


class TDSynOneStepSynthesizer(Synthesizer):
    """Demonstrative single-step expansion using one type-directed action.

    Applies its action (see :data:`ONE_STEP_ACTIONS`) exactly *once* to the
    hole and returns the result: the first complete candidate that validates
    when one exists, otherwise the first partial expansion, whose remaining
    holes are renamed to fresh ``?<fun>_goal_<i>`` subgoals so the step can be
    applied again. Deliberately performs no search — ``tdsyn`` is the backend
    that actually synthesizes a complete, valid term.
    """

    supports_deterministic_budget = True

    supports_optimization = False

    def __init__(self, action: str):
        assert action in ONE_STEP_ACTIONS
        self.action = action

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
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        skip = make_skip_fn(fun_name, metadata)
        start_time = monotonic_ns()
        ui.register(None, None, 0, True)

        # Peel abstractions from the target type. The ``backward_abs`` tactic
        # *is* the abstraction-introduction step, so it acts on the unpeeled
        # goal instead (peeling would leave it nothing to do).
        initial_term: Term
        if self.action == "backward_abs":
            initial_term, hole = fresh_hole(type, ctx)
        else:
            initial_term, _, _, initial_holes = _peel_abstractions(type, ctx)
            hole = initial_holes[0]

        action_fn = ONE_STEP_ACTIONS[self.action]
        try:
            candidates = action_fn(hole, skip)
        except Exception as e:
            raise SynthesisNotSuccessful(f"TDSynOneStepSynthesizer ({self.action}): action failed: {e}")

        partial: Term | None = None
        for replacement, new_holes in candidates:
            term = substitute_hole(initial_term, hole.name, replacement)
            feasible = (
                validate.feasible(term)
                if isinstance(validate, QTTValidator)
                else not check_linearity(Annotation(term, type), ctx)
            )
            if not feasible:
                continue
            if not new_holes:
                try:
                    if validate(term):
                        ui.register(term, [], _get_elapsed_time(start_time), True)
                        return term
                except Exception:
                    continue
            elif partial is None:
                partial = term

        if partial is not None:
            partial = _rename_subgoals(partial, fun_name)
            ui.register(partial, [], _get_elapsed_time(start_time), True)
            return partial

        raise SynthesisNotSuccessful(
            f"TDSynOneStepSynthesizer: the {self.action} action produced no candidates for this hole"
        )
