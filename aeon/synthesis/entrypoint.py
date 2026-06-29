from __future__ import annotations

import time
from typing import Any, Optional
from typing import Callable
from typing import TypeAlias

import multiprocess as mp
from loguru import logger

import aeon.logger.logger  # noqa: F401  — registers custom levels (SYNTHESIZER etc.) at import.

from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution

import dataclasses

from aeon.core.terms import (
    Let,
    Literal,
    Rec,
    Term,
    Var,
)
from aeon.core.types import Top
from aeon.core.types import top, Type
from aeon.decorators import Metadata
from aeon.synthesis.scope import shadow_fitness_helpers
from aeon.backend.evaluator import eval
from aeon.synthesis.uis.api import SynthesisUI
from aeon.synthesis.identification import get_holes_info
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name

from aeon.synthesis.api import (
    ErrorInSynthesis,
    InvalidIndividualException,
    ProgramSynthesizer,
    Synthesizer,
    TimeoutInEvaluationException,
)
from aeon.synthesis.evaluation_pool import EvalPrimitives, EvaluationPool, set_program_tail
from aeon.synthesis.modules.contata.cosynthesis import (
    _cosynthesize_group,
    _joint_accepts,  # noqa: F401  — re-exported for tests/external callers.
    _refine_obligations,  # noqa: F401  — re-exported for tests/external callers.
    _smt_unsat_core_obligations,  # noqa: F401  — re-exported for tests/external callers.
)
from aeon.synthesis.tactics.explicit_synth import ExplicitTacticSynthesizer

from aeon.synthesis.decorators import Goal
from aeon.synthesis.resource_meters import measure_cputime, measure_energy


def make_program(whole_program: Term, hole_name: Name) -> Callable[[Term], Term]:
    def replace(candidate: Term) -> Term:
        return substitution(whole_program, candidate, hole_name)

    return replace


def make_validator(ctx: TypingContext, replace: Callable[[Term], Term]) -> Callable[[Term], bool]:
    def validate(candidate: Term) -> bool:
        prog = replace(candidate)
        return check_type(ctx, prog, Top())

    return validate


Evaluators: TypeAlias = list[Callable[[Term], float]]


def _ectx_for_workers(ectx: EvaluationContext) -> EvaluationContext:
    return EvaluationContext(
        ectx.variables,
        metadata=ectx.metadata,
        pipeline=None,
        trace=ectx.trace,
        trace_stack=ectx.trace_stack,
    )


def _make_fitness(goal: Goal, ectx: EvaluationContext) -> Callable[[Term], float]:
    """Build a fitness function for a single goal, dispatching on ``goal.kind``."""

    def fitness(v: Term) -> float:
        # Evaluate the goal's objective function (a nullary top-level binding,
        # e.g. ``jaccard shape``) by making it the program's result. Replacing
        # the program tail works whether or not a ``main`` entry point is
        # present -- under ``--no-main`` there is none, and the previous
        # ``main``-substitution silently left the metric uncomputed (the program
        # evaluated to its placeholder tail instead of the objective).
        program_for_fitness = set_program_tail(v, Var(goal.function))
        try:
            if goal.kind == "cputime":
                return measure_cputime(lambda: eval(program_for_fitness, ectx))
            if goal.kind == "energy":
                return measure_energy(lambda: eval(program_for_fitness, ectx))
            return eval(program_for_fitness, ectx)
        except Exception:
            # A candidate that crashes mid-evaluation has no well-defined
            # fitness. Returning ``sys.maxsize`` made it "infinitely good"
            # for ``@maximize_*`` and "infinitely bad" for ``@minimize_*``
            # at the same time — a hybrid the Pareto front cannot dominate,
            # so a single crash would lock in as "Best" forever (issue
            # #120). Raise the backend-neutral
            # ``InvalidIndividualException`` instead; synthesizer adapters
            # translate it into their search framework's notion of "drop
            # this candidate".
            raise InvalidIndividualException()

    return fitness


def make_evaluators(ectx: EvaluationContext, fun_name: Name, metadata: Metadata) -> Evaluators:
    """Returns a list of functions that take the original program and return each fitness value"""

    goals: list[Goal] = metadata.get(fun_name, {}).get("goals", [])
    fitnesses: list[Callable[[Term], float]] = []
    for goal in goals:
        assert goal.length == 1, "Currently, we only support 1 fitness value per function"
        fitnesses.append(_make_fitness(goal, ectx))
    return fitnesses


def make_evaluator(
    ectx: EvaluationContext, replace: Callable[[Term], Term], evaluators: Evaluators, budget_eval: float = 1.0
) -> Callable[[Term], list[float]]:
    """Creates a function that takes candidate programs and return the fitness list."""

    def evaluate_individual(program: Any, result_queue: mp.Queue) -> Any:
        """Function to run in a separate process and places the result in a Queue."""
        start = time.time()
        try:
            try:
                results = [ev(program) for ev in evaluators]
                assert isinstance(results, list)
                result_queue.put(("ok", results))
            except InvalidIndividualException:
                result_queue.put(("invalid", None))
        except Exception as e:
            logger.log("SYNTHESIZER", f"Failed in the fitness function: {e}, {type(e)}")
            # Make sure the parent isn't left blocked on ``result_queue.get()``
            # if an unexpected exception escapes — propagate it as a typed
            # message so the parent re-raises ``ErrorInSynthesis``.
            result_queue.put(("error", f"{type(e).__name__}: {e}"))
            raise ErrorInSynthesis(e, msg=f"Failed in the fitness function: {e}, {type(e)}")
        finally:
            end = time.time()
            logger.info(f"Individual evaluation time: {end - start} ")

    def evaluate(candidate: Term, timeout: float = budget_eval) -> list[float]:
        # import faulthandler; faulthandler.enable()
        prog = replace(candidate)
        result_queue = mp.Queue()
        eval_process = mp.Process(target=evaluate_individual, args=(prog, result_queue))
        eval_process.start()
        eval_process.join(timeout=timeout)
        if eval_process.is_alive():
            # Order matters: ``Process.close()`` raises
            # ``ValueError: Cannot close a process while it is still running``
            # unless the process has already exited. Terminate and join first,
            # then release its resources.
            eval_process.terminate()
            eval_process.join()
            eval_process.close()
            raise TimeoutInEvaluationException()
        kind, payload = result_queue.get()
        if kind == "ok":
            return payload
        if kind == "invalid":
            raise InvalidIndividualException()
        raise ErrorInSynthesis(Exception(payload), msg=str(payload))

    return evaluate


def make_output_evaluator(
    ectx: EvaluationContext,
    replace: Callable[[Term], Term],
    hole_fun: Name,
    budget_eval: float = 1.0,
) -> Callable[[Term], Any]:
    """Build a function that evaluates a candidate to its raw *output value*.

    Where ``make_evaluator`` returns the goal's distance, this returns the value
    the candidate itself denotes (the program's "scene"/output), by setting the
    program tail to the synthesised function and evaluating it. Metric
    synthesisers use it to cluster candidates by their actual output
    (observational equivalence) rather than only by distance-to-goal. Returns
    ``None`` when the candidate cannot be evaluated (so callers can skip it).
    """

    def run(program: Term, result_queue: mp.Queue) -> None:
        try:
            value = eval(set_program_tail(program, Var(hole_fun)), ectx)
            try:
                result_queue.put(("ok", value))
            except Exception:
                # Unpicklable output: fall back to its repr so it is still
                # usable as an equivalence key across the process boundary.
                result_queue.put(("ok", repr(value)))
        except Exception as e:  # noqa: BLE001 — any failure means "no output"
            result_queue.put(("error", f"{type(e).__name__}: {e}"))

    def output(candidate: Term, timeout: float = budget_eval) -> Any:
        prog = replace(candidate)
        result_queue: mp.Queue = mp.Queue()
        proc = mp.Process(target=run, args=(prog, result_queue))
        proc.start()
        proc.join(timeout=timeout)
        if proc.is_alive():
            proc.terminate()
            proc.join()
            return None
        kind, payload = result_queue.get()
        return payload if kind == "ok" else None

    return output


def _cluster_function(metadata: Metadata, fun_name: Name) -> Optional[Name]:
    """The ``@cluster`` featuriser function for this hole, if any (robust to
    Name identity, like the goals lookup)."""
    entry = metadata.get(fun_name, {})
    c = entry.get("cluster") if isinstance(entry, dict) else None
    if c is not None:
        return c
    for _, v in metadata.items():
        if isinstance(v, dict) and v.get("cluster"):
            return v["cluster"]
    return None


def _synthesize_one(
    ctx: TypingContext,
    ectx: EvaluationContext,
    prog: Term,
    fun_name: Name,
    hole_name: Name,
    ty: Type,
    tyctx: TypingContext,
    metadata: Metadata,
    synthesizer: Synthesizer,
    budget: float,
    ui: SynthesisUI,
    budget_eval: float,
) -> Term:
    """Synthesize a single hole in ``prog``.

    ``prog`` is the whole program with this hole still open but with any sibling
    holes already filled by their current candidates (co-synthesis): so the
    candidate search sees its callees, both for the liquid-type oracle and for
    example evaluation."""
    # Let-shadow the fitness/example/cluster helpers to Unit at the hole, so
    # the synthesizer never builds them (replaces the __internal__ filter).
    tyctx = shadow_fitness_helpers(tyctx, metadata)
    ui.start(tyctx, ectx, hole_name.name, ty, budget)

    replace = make_program(prog, hole_name)
    validator = make_validator(ctx, replace)
    evaluators = make_evaluators(ectx, fun_name, metadata)
    assert isinstance(tyctx, TypingContext)
    assert isinstance(ty, Type)
    tac_map = metadata.get(fun_name, {}).get("tactic_scripts")
    steps = None
    if isinstance(tac_map, dict):
        raw = tac_map.get(hole_name)
        if raw is not None:
            steps = tuple(raw)
        elif len(tac_map) == 1:
            steps = tuple(next(iter(tac_map.values())))
    syn_impl: Synthesizer = ExplicitTacticSynthesizer(steps) if steps is not None else synthesizer

    # Evaluate every candidate on a persistent worker pool. The backend
    # declares which computations it wants run per candidate (the objective
    # ``fitness`` always; an ``output`` feature if it clusters by one, etc.);
    # the pool runs exactly those, in one round-trip, knowing nothing about
    # what they mean. A `@cluster(f shape)` decorator names the output
    # featuriser `f` (e.g. a rasterised scene), else the output is the
    # candidate's own value.
    feature_fun = _cluster_function(metadata, fun_name) or fun_name
    primitives = EvalPrimitives(evaluators, _ectx_for_workers(ectx), feature_fun, replace)
    pool = EvaluationPool(replace, syn_impl.computations(primitives), budget_eval=budget_eval)
    evaluator, output_evaluator = _pool_backed(pool)

    # Example-driven (PBE) probe: evaluate a candidate body on a concrete
    # list of input values *in process*, returning the value the synthesised
    # function produces. Unlike ``output_evaluator`` (which crosses a process
    # boundary and so can only return a candidate's repr for function-typed
    # outputs), this stays in-process, so a String -> String candidate can be
    # applied to each example's inputs. This is what lets ``afta`` build a
    # tree automaton keyed by per-example outputs (the BLAZE construction).
    if metadata.get(fun_name, {}).get("io_examples"):
        io_params: list[Name] = metadata.get(fun_name, {}).get("io_params", [])
        # Fill the hole with a harmless dummy so building the program's
        # def-environment (which includes the @example test bindings that
        # *call* the synthesised function) never reaches the unfilled hole
        # and blocks on the interactive prompt. The dummy body is irrelevant:
        # the sub-terms we probe are built from the DSL components and the
        # parameters, not from the function under synthesis.
        from aeon.core.types import t_string as _t_string

        _dummy_prog = replace(Literal("", _t_string))
        # Build the evaluation environment (all in-scope DSL bindings) ONCE,
        # rather than re-evaluating the whole def-chain for every probed
        # sub-term. Each binding is bound by evaluating it with its own name
        # as the tail, which reuses ``eval``'s Let/Rec (incl. recursion-tying)
        # handling without duplicating it.
        _base_ctx = ectx
        _t: Term = _dummy_prog
        while isinstance(_t, (Let, Rec)):
            _bound = eval(dataclasses.replace(_t, body=Var(_t.var_name)), _base_ctx)
            _base_ctx = _base_ctx.with_var(_t.var_name, _bound)
            _t = _t.body

        def _pbe_probe(sub_term: Term, input_values: list, _params=tuple(io_params), _ctx=_base_ctx) -> Any:
            # Evaluate a sub-term (open in the hole's parameters) on one
            # example's inputs, directly in the precomputed DSL environment.
            e = _ctx
            for pname, v in zip(_params, input_values):
                e = e.with_var(pname, v)
            return eval(sub_term, e)

        metadata.setdefault(fun_name, {})["pbe_probe"] = _pbe_probe

    try:
        t = syn_impl.synthesize(
            ctx=tyctx,
            type=ty,
            validate=validator,
            evaluate=evaluator,
            fun_name=fun_name,
            metadata=metadata,
            budget=budget,
            ui=ui,
            output_value=output_evaluator,
        )
    except Exception as e:
        ui.end(None, None)
        raise e
    finally:
        pool.close()

    ui.end(t, None)
    return t


def _mutual_group_ids(term: Term) -> dict[Name, Optional[int]]:
    """Map each top-level function name to its ``mutual`` group id (``None`` if
    not part of a mutual block)."""
    from aeon.synthesis.identification import iterate_top_level

    return {rec.var_name: rec.mutual_group_id for rec in iterate_top_level(term)}


def _partition_targets(
    term: Term, targets: list[tuple[Name, list[Name]]]
) -> tuple[list[tuple[Name, list[Name]]], list[list[tuple[Name, list[Name]]]]]:
    """Split synthesis targets into independent ones and mutual groups (2+
    members sharing a ``mutual_group_id``)."""
    gid_of = _mutual_group_ids(term)
    groups: dict[int, list[tuple[Name, list[Name]]]] = {}
    singles: list[tuple[Name, list[Name]]] = []
    for fun_name, holes in targets:
        gid = gid_of.get(fun_name)
        if gid is None:
            singles.append((fun_name, holes))
        else:
            groups.setdefault(gid, []).append((fun_name, holes))
    mutual: list[list[tuple[Name, list[Name]]]] = []
    for members in groups.values():
        if len(members) > 1:
            mutual.append(members)
        else:
            singles.extend(members)
    return singles, mutual


def synthesize_holes(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    targets: list[tuple[Name, list[Name]]],
    metadata: Metadata,
    synthesizer: Synthesizer | ProgramSynthesizer,
    budget: float = 60.0,
    ui: SynthesisUI = SynthesisUI(),
    budget_eval: Optional[float] = None,
    constructor_names: set[str] | None = None,
) -> dict[Name, Optional[Term]]:
    """Synthesizes code for multiple functions, each with one hole.

    Independent functions are synthesised one at a time. Members of a Lean
    ``mutual ... end`` block are co-synthesised together (Contata's relational
    recursive synthesis), so a candidate for one member may call its siblings.
    ``constructor_names`` (data-constructor names) is forwarded to the
    ``@property`` runner used as a relational/k-safety acceptance oracle."""

    # Program-level synthesizers (e.g. joint Float-hole optimisation) fill every
    # hole at once rather than one function at a time.
    if isinstance(synthesizer, ProgramSynthesizer):
        return synthesizer.synthesize_program(ctx, ectx, term, targets, metadata, budget, ui)

    if budget_eval is None:
        budget_eval = max(budget / 1000, 1)

    program_holes = get_holes_info(ctx, term, top, targets, refined_types=True)

    mapping: dict[Name, Optional[Term]] = {}

    singles, mutual_groups = _partition_targets(term, targets)

    for fun_name, holes_names in singles:
        assert len(holes_names) == 1, "Currently, we only support 1 hole per function"
        hole_name = holes_names[0]
        ty, tyctx = program_holes[hole_name]
        assert isinstance(tyctx, TypingContext)
        mapping[hole_name] = _synthesize_one(
            ctx, ectx, term, fun_name, hole_name, ty, tyctx, metadata, synthesizer, budget, ui, budget_eval
        )

    for group in mutual_groups:
        for fun_name, holes_names in group:
            assert len(holes_names) == 1, "Currently, we only support 1 hole per function"
        mapping.update(
            _cosynthesize_group(
                ctx,
                ectx,
                term,
                group,
                program_holes,
                metadata,
                synthesizer,
                budget,
                ui,
                budget_eval,
                constructor_names=constructor_names,
            )
        )

    return mapping


def _pool_backed(pool: EvaluationPool) -> tuple[Callable[[Term], list[float]], Callable[[Term], Any]]:
    """Adapt a pool to the ``(evaluate, output_value)`` callables the synthesiser
    interface expects: ``evaluate`` reads the ``fitness`` computation, and
    ``output_value`` the ``output`` one. Each candidate is run once (all its
    computations together) and the results cached, so the two callables share
    that single round-trip."""
    cache: dict[str, dict[str, tuple[str, Any]]] = {}

    def results(term: Term) -> dict[str, tuple[str, Any]]:
        key = str(term)
        if key not in cache:
            cache[key] = pool.run(term)
        return cache[key]

    def evaluate(term: Term) -> list[float]:
        status, value = results(term).get("fitness", ("ok", []))
        if status == "invalid":
            raise InvalidIndividualException()
        if status == "timeout":
            raise TimeoutInEvaluationException()
        if status == "error":
            raise ErrorInSynthesis(Exception(value), msg=str(value))
        return value if value is not None else []

    def output_value(term: Term) -> Any:
        status, value = results(term).get("output", ("error", None))
        return value if status == "ok" else None

    return evaluate, output_value
