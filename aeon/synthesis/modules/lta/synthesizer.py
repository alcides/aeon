"""LTASynthesize algorithm (Algorithm 1 of the paper) wrapped as an aeon
`Synthesizer`.

LTASynthesize(F, φ, k):
    A0 ← WF(F, A⊥);  E ← ∅
    if NEmpty(A0):  return (A0, ⋃ ⟦q⟧)
    return Enumerate(A0, φ, k)

Enumerate(A, φ, k):
    if depth(A) < k:
        A   ← Transition(F, A)
        A   ← Prune(A)
        E   ← Similarity(A, E)
        (Amin, E) ← Minimize(A, E)
        if NEmpty(Amin):  return (Amin, ⋃ ⟦q⟧)
        Enumerate(Amin, φ, k)
    else:
        return ⊥
"""

from __future__ import annotations

import time
from typing import Callable

from loguru import logger

from aeon.core.terms import Abstraction, Term
from aeon.core.types import AbstractionType, Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

from aeon.synthesis.modules.lta.automaton import (
    LTA,
    State,
    language,
    nonempty_finals,
)
from aeon.synthesis.modules.lta.construction import (
    TypeContextLTA,
    e_app,
    e_const,
    e_poly_var,
    e_tapp,
    e_var,
    q_goal,
)
from aeon.synthesis.modules.lta.cyclic import build_universe, well_formed_constraints
from aeon.synthesis.modules.lta.polymorphism import (
    collect_type_universe,
    is_polymorphic,
    monomorphize,
)
from aeon.synthesis.modules.lta.reductions import minimize, prune, similarity


_loc = SynthesizedLocation("lta")


class LTASynthesizer(Synthesizer):
    """Component-based synthesis via Liquid Tree Automata.

    The algorithm iteratively expands a `well-formed' LTA built from the
    library `F` (the typing context's library functions) and a goal type
    `φ`, applying the rules of Fig. 7 and the reductions of Fig. 9.

    The implementation simulates a single goal state at depth ≤ `max_depth`.
    """

    def __init__(self, max_depth: int = 4):
        self.max_depth = max_depth

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
    ) -> Term:
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        current_metadata = metadata.get(fun_name, {})
        hidden_names = {v.name for v in current_metadata.get("hide", [])}
        if hidden_names:
            filtered = [e for e in ctx.entries if not (isinstance(e, VariableBinder) and e.name.name in hidden_names)]
            ctx = TypingContext(filtered)

        start = time.time()
        ui.register(None, None, 0, True)

        # Peel any function abstractions off the goal type. The body is the
        # actual synthesis target; the parameters are added to the context.
        inner_type, inner_ctx, abs_names = _peel_abstractions(type, ctx)

        # Build initial LTA A0.
        lta = LTA()
        tctx = TypeContextLTA.empty()

        # Build the cyclic universe states qt / qϕ (Paper §5). The finite type
        # universe — built-ins plus every base type mentioned in Γ and φ —
        # is what polymorphic type variables get instantiated against.
        universe_types = collect_type_universe(inner_ctx, inner_type)
        tctx.universe = build_universe(lta, ctx, universe_types)

        # E-var / E-poly-var transitions for every binding in Γ. Polymorphic
        # bindings additionally get monomorphic E-tapp instantiations so that
        # concrete candidate terms can be enumerated (the cyclic poly state is
        # the §5 template; the E-tapp states are its bounded unrolling).
        for name, ty in inner_ctx.concrete_vars():
            if is_polymorphic(ty):
                e_poly_var(lta, tctx, name, ty)
                for inst in monomorphize(name, ty, universe_types):
                    e_tapp(lta, tctx, inst.term, inst.mono_type)
            else:
                e_var(lta, tctx, name, ty)

        # Minimal constant repertoire (E-const).
        from aeon.core.types import t_bool, t_int

        e_const(lta, tctx, 0, t_int)
        e_const(lta, tctx, 1, t_int)
        e_const(lta, tctx, True, t_bool)
        e_const(lta, tctx, False, t_bool)

        # Verify the acyclic-constraint restriction (§5): no constrained
        # transition may reference a state that participates in a cycle.
        ok, violations = well_formed_constraints(lta)
        if not ok:
            logger.debug(f"lta: acyclic-constraint violations: {violations}")

        # Try to satisfy the goal directly with a size-1 candidate.
        if _try_goal(lta, tctx, inner_type, inner_ctx):
            term = _extract_solution(lta, abs_names)
            if term is not None and self._accept(term, validate):
                ui.register(term, [], time.time() - start, True)
                return term

        # Enumerate: explore-reduce-check loop.
        equiv_set: set[tuple[int, int]] = set()
        depth = 1
        while depth < self.max_depth and (time.time() - start) < budget:
            new_states = _transition_step(lta, tctx, inner_ctx)
            if not new_states:
                break
            lta = prune(lta, inner_ctx)
            equiv_set = similarity(lta, inner_ctx, equiv_set)
            lta, equiv_set = minimize(lta, equiv_set)

            if _try_goal(lta, tctx, inner_type, inner_ctx):
                term = _extract_solution(lta, abs_names)
                if term is not None and self._accept(term, validate):
                    ui.register(term, [], time.time() - start, True)
                    return term
            depth += 1

        raise SynthesisNotSuccessful(f"LTASynthesizer: no solution within depth={self.max_depth}, budget={budget}s")

    @staticmethod
    def _accept(term: Term, validate: Callable[[Term], bool]) -> bool:
        try:
            return validate(term)
        except Exception as e:
            logger.debug(f"lta: validate failed for {term}: {e}")
            return False


def _peel_abstractions(ty: Type, ctx: TypingContext) -> tuple[Type, TypingContext, list[Name]]:
    """Strip leading function arrows, extending the context with their
    binders and returning the inner body type."""
    cur = ty
    cur_ctx = ctx
    names: list[Name] = []
    while isinstance(cur, AbstractionType):
        names.append(cur.var_name)
        cur_ctx = cur_ctx.with_var(cur.var_name, cur.var_type)
        cur = cur.type
    return cur, cur_ctx, names


def _transition_step(lta: LTA, tctx: TypeContextLTA, type_ctx: TypingContext) -> list[State]:
    """One round of E-app expansion: pair every function state with every
    argument state and try to introduce a new `app` transition. Returns the
    set of newly-created expression states.

    Raw `forall`-typed states (the §5 polymorphic *templates* produced by
    `e_poly_var`) are skipped — aeon's subtyping treats them as trivially
    compatible. Their *instantiated* `e_tapp` states carry concrete
    monomorphic types and therefore participate normally: an instantiated
    polymorphic function like `id[Int] : (x:Int) -> Int` enters the function
    pool just like any monomorphic library function.
    """
    function_states: list[State] = []
    arg_states: list[State] = []
    for s in list(lta.states):
        if s.aeon_type is None or s.is_type_state:
            continue
        if is_polymorphic(s.aeon_type):
            continue  # §5 template — only its e_tapp instances are concrete
        if isinstance(s.aeon_type, AbstractionType):
            function_states.append(s)
        else:
            arg_states.append(s)

    new_states: list[State] = []
    for q_f in function_states:
        for q_a in arg_states:
            q_app = e_app(lta, tctx, q_f, q_a, type_ctx)
            if q_app is not None:
                new_states.append(q_app)
    return new_states


def _try_goal(lta: LTA, tctx: TypeContextLTA, goal_type: Type, type_ctx: TypingContext) -> bool:
    """Try to connect every candidate term-state to the goal type via Q-goal.
    Returns True if at least one final state's denotation is non-empty.

    Raw `forall`-typed template states are excluded — aeon's subtyping treats
    them as `ctrue` against any target. Their concrete `e_tapp` instantiations
    (monomorphic types) are included and goal-checked normally.
    """
    candidates = [
        s
        for s in lta.states
        if not s.is_type_state
        and s.aeon_type is not None
        and not isinstance(s.aeon_type, AbstractionType)
        and not is_polymorphic(s.aeon_type)
    ]
    for q in candidates:
        q_goal(lta, tctx, goal_type, q, type_ctx)
    return bool(nonempty_finals(lta))


def _extract_solution(lta: LTA, abs_names: list[Name]) -> Term | None:
    """Pull a concrete term from the LTA's language and wrap it in the
    abstractions that were peeled off the goal type."""
    terms = language(lta, max_terms_per_state=4)
    if not terms:
        return None
    term: Term = terms[0]
    for name in reversed(abs_names):
        term = Abstraction(name, term, _loc)
    return term
