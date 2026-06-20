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
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidTerm
from aeon.core.substitutions import substitution
from aeon.core.terms import Literal, Term
from aeon.core.types import RefinedType, Type, TypeConstructor, t_float, top
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


def _unrefine(ty: Type) -> Type:
    return ty.type if isinstance(ty, RefinedType) else ty


def _is_float(ty: object) -> bool:
    base = _unrefine(ty) if isinstance(ty, Type) else ty
    return isinstance(base, TypeConstructor) and base.name.name == "Float"


def _is_array_float(ty: object) -> bool:
    base = _unrefine(ty) if isinstance(ty, Type) else ty
    return (
        isinstance(base, TypeConstructor)
        and base.name.name == "Array"
        and len(base.args) == 1
        and _is_float(base.args[0])
    )


def _size_app(lt: LiquidTerm) -> bool:
    """A liquid application of an array length measure (e.g. ``Array_size``)."""
    return isinstance(lt, LiquidApp) and "size" in getattr(lt.fun, "name", str(lt.fun)).lower()


def _array_length(ty: Type) -> int | None:
    """Extract ``k`` from an ``Array`` hole refined by ``size a == k``.

    Walks the refinement looking for an equality between an array-size
    application and an integer literal (either operand order, anywhere in a
    conjunction). Returns ``None`` if no such constraint is present.
    """
    if not isinstance(ty, RefinedType):
        return None
    found: list[int] = []

    def walk(lt: LiquidTerm) -> None:
        if isinstance(lt, LiquidApp):
            fname = getattr(lt.fun, "name", str(lt.fun))
            if fname == "==" and len(lt.args) == 2:
                a, b = lt.args
                for x, y in ((a, b), (b, a)):
                    if _size_app(x) and isinstance(y, LiquidLiteralInt):
                        found.append(y.value)
            for a in lt.args:
                walk(a)

    walk(ty.refinement)
    return found[0] if found else None


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

        # Map each hole to a contiguous slice of one flat float vector: a scalar
        # ``Float`` hole takes one dimension, an ``(Array Float)`` hole takes one
        # dimension per element (its length comes from a ``size a == k``
        # refinement). Order is stable, taken from the targets.
        hole_names = [h for _, holes in targets for h in holes]
        holes_info = get_holes_info(ctx, term, top, targets, refined_types=True)

        # spec = (hole name, literal type to substitute, number of dimensions, is_array)
        specs: list[tuple[Name, Type, int, bool]] = []
        bad: list[str] = []
        for h in hole_names:
            ty = holes_info[h][0]
            base = _unrefine(ty)
            if _is_float(base):
                specs.append((h, t_float, 1, False))
            elif _is_array_float(base):
                k = _array_length(ty)
                if k is None or k < 1:
                    bad.append(f"{h.pretty()} (Array Float without a 'size a == k' refinement)")
                else:
                    specs.append((h, base, k, True))
            else:
                bad.append(f"{h.pretty()} (type {base})")

        total_dims = sum(k for _, _, k, _ in specs)
        if bad or total_dims < 2:
            raise SynthesisError(
                "FloatHoleNG only applies to holes that are Float or (Array Float) with a fixed "
                "'size a == k' refinement, totalling at least two float dimensions. "
                + (f"Unsupported holes: {bad}. " if bad else f"Only {total_dims} dimension(s). ")
                + "Use a grammar-based synthesizer (e.g. -s ng / gp) instead."
            )

        # The objective(s) live on whichever function carries the @minimize/
        # @maximize decorator — not necessarily one of the hole-bearing
        # functions — so collect goals across the whole program.
        goals: list[Goal] = [g for d in metadata.values() for g in d.get("goals", [])]
        if not goals:
            raise SynthesisError("FloatHoleNG requires at least one @minimize/@maximize objective on the program.")
        evaluators = [_make_fitness(g, ectx) for g in goals]
        minimize = [g.minimize for g in goals]
        n = total_dims

        def decode(vec: list[float]) -> dict[Name, Optional[Term]]:
            """Split the flat vector into one term per hole (scalar → Float
            literal, array slice → list-valued ``Array Float`` literal)."""
            mapping: dict[Name, Optional[Term]] = {}
            i = 0
            for name, lit_type, k, is_array in specs:
                chunk = vec[i : i + k]
                i += k
                if is_array:
                    mapping[name] = Literal([float(x) for x in chunk], type=lit_type)
                else:
                    mapping[name] = Literal(float(chunk[0]), type=lit_type)
            return mapping

        def fill(vec: list[float]) -> Term:
            prog = term
            for name, rep in decode(vec).items():
                assert rep is not None
                prog = substitution(prog, rep, name)
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
        return decode(best_vec)
