"""FloatHoleNG: joint Nevergrad optimisation of a program's Float holes.

Where :class:`~aeon.synthesis.grammar.genomic_ng.GenomicNGSynthesizer` searches
a *grammar* for one hole at a time, this synthesizer targets a narrower but very
common shape: a program whose holes are **all of type ``Float``**, jointly
driving one (or more) ``@minimize``/``@maximize`` objective. There the search
space is simply an **array of floats — one dimension per hole** — and the
problem is exactly the continuous black-box optimisation Nevergrad is built for
(this is how Nevergrad's own benchmark functions — sphere, Rosenbrock,
Rastrigin, Ackley — are posed).

Each candidate float vector is substituted into the holes as ``Float`` literals;
the resulting hole-free program is evaluated through the existing objective
machinery (``_make_fitness``); Nevergrad minimises the (orientation-corrected)
result.
"""

from __future__ import annotations

import time
from typing import Optional

from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
from aeon.core.terms import Literal, Term
from aeon.core.types import TypeConstructor, t_float, top
from aeon.decorators.api import Metadata
from aeon.synthesis.api import ProgramSynthesizer, SynthesisError
from aeon.synthesis.decorators import Goal
from aeon.synthesis.entrypoint import _make_fitness
from aeon.synthesis.grammar.genomic_ng import INVALID_PENALTY, _knee_point, _orient
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

from geneticengine.problems import Fitness

# Default symmetric search box for each float hole. Covers the standard domains
# of the classic Nevergrad benchmark functions (sphere/Rastrigin/Ackley use
# ±5.12, Rosenbrock ±2.048); overridable per synthesizer instance.
DEFAULT_BOUND = 5.12

# Evaluation budget declared to the Nevergrad optimiser. Several optimisers
# (notably NGOpt) tune their internal strategy to this number; an over-large
# value makes them pick heavy portfolio methods whose per-``ask`` overhead
# dominates when each fitness evaluation is cheap (a few hundred microseconds
# here). A moderate value keeps ``ask`` fast — the wall-clock budget is the real
# stop, and Nevergrad happily accepts more asks than its declared budget.
OPTIMIZER_BUDGET = 1000


def _is_float(ty: object) -> bool:
    return isinstance(ty, TypeConstructor) and ty.name.name == "Float"


class FloatHoleNGSynthesizer(ProgramSynthesizer):
    """Joint Float-hole optimisation with Nevergrad.

    Args:
        optimizer: name of a Nevergrad optimiser class (``"NGOpt"``, ``"CMA"``,
            ``"DE"``, ``"PSO"``, ...).
        seed: seed for the optimiser and its parametrization.
        bound: each hole is searched in ``[-bound, bound]``.
    """

    def __init__(self, optimizer: str = "NGOpt", seed: int = 0, bound: float = DEFAULT_BOUND):
        self.optimizer = optimizer
        self.seed = seed
        self.bound = bound

    def synthesize_program(
        self,
        ctx: TypingContext,
        ectx: EvaluationContext,
        term: Term,
        targets: list[tuple[Name, list[Name]]],
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> dict[Name, Optional[Term]]:
        try:
            import nevergrad as ng
        except ImportError as e:  # pragma: no cover - optional dependency
            raise ImportError(
                "FloatHoleNG requires the 'nevergrad' package. Install it with "
                "`uv pip install nevergrad` (or the 'synthesis-ng' extra)."
            ) from e

        # One float dimension per hole, in a stable order taken from the targets.
        hole_names = [h for _, holes in targets for h in holes]
        holes_info = get_holes_info(ctx, term, top, targets, refined_types=False)
        non_float = [h for h in hole_names if not _is_float(holes_info[h][0])]
        if len(hole_names) < 2 or non_float:
            raise SynthesisError(
                "FloatHoleNG only applies to programs with two or more holes, all of type Float. "
                f"Got {len(hole_names)} hole(s)"
                + (f"; non-Float: {[h.pretty() for h in non_float]}" if non_float else "")
                + ". Use a grammar-based synthesizer (e.g. -s ng / gp) instead."
            )

        # The objective(s) live on whichever function carries the @minimize/
        # @maximize decorator — not necessarily one of the hole-bearing
        # functions — so collect goals across the whole program.
        goals: list[Goal] = [g for d in metadata.values() for g in d.get("goals", [])]
        if not goals:
            raise SynthesisError("FloatHoleNG requires at least one @minimize/@maximize objective on the program.")
        evaluators = [_make_fitness(g, ectx) for g in goals]
        minimize = [g.minimize for g in goals]
        n = len(hole_names)

        def fill(vec: list[float]) -> Term:
            prog = term
            for name, val in zip(hole_names, vec):
                prog = substitution(prog, Literal(float(val), type=t_float), name)
            return prog

        def evaluate(vec: list[float]) -> list[float]:
            prog = fill(vec)
            # _make_fitness raises InvalidIndividualException on an un-evaluable
            # candidate; let it (and anything else) propagate to the penalty path.
            return [ev(prog) for ev in evaluators]

        parametrization = ng.p.Array(shape=(n,)).set_bounds(-self.bound, self.bound)
        parametrization.random_state.seed(self.seed)
        opt_cls = ng.optimizers.registry[self.optimizer]
        optimizer = opt_cls(parametrization=parametrization, budget=OPTIMIZER_BUDGET, num_workers=1)

        ui.start(ctx, ectx, "+".join(h.name for h in hole_names), top, budget)

        archive: list[tuple[tuple[float, ...], list[float]]] = []
        best_vec: list[float] | None = None
        best_score: float | None = None
        start = time.monotonic()

        while time.monotonic() - start < budget:
            candidate = optimizer.ask()
            vec = [float(x) for x in candidate.value]
            try:
                components = evaluate(vec)
                oriented = _orient(components, minimize)
                valid = True
            except Exception:
                components = [INVALID_PENALTY] * len(minimize)
                oriented = list(components)
                valid = False

            loss = oriented if len(oriented) > 1 else oriented[0]
            optimizer.tell(candidate, loss)

            if valid:
                archive.append((tuple(vec), oriented))
                score = sum(oriented)
                if best_score is None or score < best_score:
                    best_score, best_vec = score, vec
                    ui.register(fill(vec), Fitness(components, valid=True), time.monotonic() - start, is_best=True)

        if best_vec is None:
            ui.end(None, None)
            return {h: None for h in hole_names}

        # For multiple objectives the scalar ``best_vec`` is just one Pareto
        # point; resolve the archive by knee-point compromise to match the
        # grammar backend's behaviour.
        if len(minimize) > 1:
            chosen = _knee_point(archive, minimize)
            if chosen is not None:
                best_vec = list(chosen)

        ui.end(fill(best_vec), None)
        return {h: Literal(float(v), type=t_float) for h, v in zip(hole_names, best_vec)}
