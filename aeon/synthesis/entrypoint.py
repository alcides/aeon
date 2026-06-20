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
    Abstraction,
    Annotation,
    Application,
    If,
    Let,
    Literal,
    Rec,
    RefinementApplication,
    Term,
    TypeApplication,
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
    primitives = EvalPrimitives(evaluators, ectx, feature_fun, replace)
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


def _value_literal(v: Any) -> Optional[Term]:
    """Wrap a concrete scalar value back into a ``Literal`` term (for building a
    call to probe in instrumented evaluation)."""
    from aeon.core.types import t_bool, t_float, t_int, t_string

    if isinstance(v, bool):
        return Literal(v, t_bool)
    if isinstance(v, int):
        return Literal(v, t_int)
    if isinstance(v, float):
        return Literal(v, t_float)
    if isinstance(v, str):
        return Literal(v, t_string)
    return None


def _z3_value(v: Any, val_sort, consts: dict, rev: dict):
    """Encode a concrete scalar/opaque value as a z3 term. Ints/bools/reals map to
    their native sorts; everything else (lists, ADTs, ...) maps to distinct
    constants of an uninterpreted sort, with ``rev`` recording the inverse so a
    model value can be decoded back."""
    import z3

    if isinstance(v, bool):
        return z3.BoolVal(v)
    if isinstance(v, int):
        return z3.IntVal(v)
    if isinstance(v, float):
        return z3.RealVal(v)
    key = ("str", v) if isinstance(v, str) else ("repr", repr(v))
    if key not in consts:
        c = z3.Const(f"v{len(consts)}", val_sort)
        consts[key] = c
        rev[c.get_id()] = v
    return consts[key]


def _z3_sort(v: Any, val_sort):
    import z3

    if isinstance(v, bool):
        return z3.BoolSort()
    if isinstance(v, int):
        return z3.IntSort()
    if isinstance(v, float):
        return z3.RealSort()
    return val_sort


def _smt_unsat_core_obligations(
    spec_facts: list[tuple[Name, tuple, Any]],
    observed_facts: list[tuple[Name, tuple, Any]],
    symbolic_eqs: list[tuple[tuple[Name, tuple], tuple[Name, tuple]]],
    member_names: set[str],
    relational: list | None = None,
) -> list[tuple[Name, tuple, Any]]:
    """Contata's joint validity check + unsat-core refinement (Algorithm 2,
    lines 11-16), discharged by z3.

    The functions under synthesis are modelled as **uninterpreted functions**.
    We assert (with tracking literals) the ground spec ``ψ`` (``spec_facts``),
    the candidate's observed calls ``θ`` on inputs *not* pinned by the spec
    (``observed_facts``), the symbolic relations the candidate's structure
    induces between calls (``symbolic_eqs``, e.g. ``even(2) = odd(1)``), and any
    ``relational`` constraints — a **relational/k-safety ``@property`` evaluated
    at a counterexample**, encoded as a small IR over the same uninterpreted
    functions (e.g. ``even(2) = !odd(2)``). If the conjunction is satisfiable the
    joint candidate is consistent (no refinement). Otherwise z3's **unsat core**
    names the conflicting calls; for each blamed call to a function under
    synthesis we read its spec-consistent output from a model of
    ``ψ ∧ structure ∧ relational`` and return it as a new obligation — the
    constraint to add to that callee's next-round search."""
    import z3

    val_sort = z3.DeclareSort("Val")
    consts: dict = {}
    rev: dict = {}

    funcs: dict[str, Any] = {}

    def func_of(fname: Name, args: tuple, out: Any):
        key = fname.name
        if key not in funcs:
            arg_sorts = [_z3_sort(a, val_sort) for a in args]
            funcs[key] = z3.Function(key, *arg_sorts, _z3_sort(out, val_sort))
        return funcs[key]

    def app(fname: Name, args: tuple):
        f = funcs[fname.name]
        return f(*[_z3_value(a, val_sort, consts, rev) for a in args])

    for fname, args, out in list(spec_facts) + list(observed_facts):
        func_of(fname, args, out)

    def ir_to_z3(ir):
        """Translate a relational-property IR node into a z3 expression over the
        (already-declared) uninterpreted functions. Raises on an undeclared
        function or unsupported node, so the caller can skip that constraint."""
        tag = ir[0]
        if tag == "val":
            return _z3_value(ir[1], val_sort, consts, rev)
        if tag == "app":
            return funcs[ir[1]](*[_z3_value(a, val_sort, consts, rev) for a in ir[2]])
        if tag == "not":
            return z3.Not(ir_to_z3(ir[1]))
        if tag == "bin":
            op, a, b = ir[1], ir_to_z3(ir[2]), ir_to_z3(ir[3])
            return {
                "==": lambda: a == b,
                "!=": lambda: a != b,
                "&&": lambda: z3.And(a, b),
                "||": lambda: z3.Or(a, b),
                "<": lambda: a < b,
                "<=": lambda: a <= b,
                ">": lambda: a > b,
                ">=": lambda: a >= b,
            }[op]()
        raise ValueError(f"unsupported relational IR: {ir}")

    pinned = {(f.name, args) for f, args, _ in spec_facts}

    solver = z3.Solver()
    solver.set(unsat_core=True)
    label_of: dict = {}
    n = 0

    def track(formula, tag):
        nonlocal n
        lit = z3.Bool(f"p{n}")
        n += 1
        solver.assert_and_track(formula, lit)
        label_of[lit.get_id()] = tag

    for fname, args, out in spec_facts:
        track(app(fname, args) == _z3_value(out, val_sort, consts, rev), ("spec", fname, args, out))
    for fname, args, out in observed_facts:
        if (fname.name, args) in pinned:
            continue  # the spec is the ground truth for these calls
        track(app(fname, args) == _z3_value(out, val_sort, consts, rev), ("obs", fname, args, out))
    for (f, fa), (g, ga) in symbolic_eqs:
        if f.name in funcs and g.name in funcs:
            track(app(f, fa) == app(g, ga), ("sym", f, fa, g, ga))
    rel_z3: list = []
    for ir in relational or []:
        try:
            rel_z3.append(ir_to_z3(ir))
        except Exception:
            pass  # references an undeclared function / unsupported shape: skip
    for i, rz in enumerate(rel_z3):
        track(rz, ("rel", i))

    if solver.check() != z3.unsat:
        return []  # consistent (or unknown): nothing to refine

    core_ids = {c.get_id() for c in solver.unsat_core()}
    blamed = [label_of[i] for i in core_ids if i in label_of and label_of[i][0] == "obs"]
    if not blamed:
        return []

    # Read the spec-consistent intended outputs from a model of
    # ψ ∧ structure ∧ relational (the relational property is part of the
    # intended spec, so the model must satisfy it — that is what pins a blamed
    # callee's output, e.g. ``odd(1) = true`` from ``even(1) = !odd(1)``).
    model_solver = z3.Solver()
    for fname, args, out in spec_facts:
        model_solver.add(app(fname, args) == _z3_value(out, val_sort, consts, rev))
    for (f, fa), (g, ga) in symbolic_eqs:
        if f.name in funcs and g.name in funcs:
            model_solver.add(app(f, fa) == app(g, ga))
    for rz in rel_z3:
        model_solver.add(rz)
    if model_solver.check() != z3.sat:
        return []
    model = model_solver.model()

    def decode(z3val):
        if z3.is_int_value(z3val):
            return z3val.as_long()
        if z3.is_true(z3val):
            return True
        if z3.is_false(z3val):
            return False
        if z3.is_rational_value(z3val):
            return float(z3val.as_fraction())
        return rev.get(z3val.get_id())

    obligations: list[tuple[Name, tuple, Any]] = []
    for _tag, fname, args, obs in blamed:
        if fname.name not in member_names:
            continue
        required = decode(model.eval(app(fname, args), model_completion=False))
        if required is not None and required != obs:
            obligations.append((fname, args, required))
    return obligations


def _trivial_stub(ty: Type) -> Optional[Term]:
    """A constant value of ``ty``'s base carrier, used to stand in for a not-yet-
    synthesised sibling during co-synthesis so example evaluation never reaches a
    raw hole (the executable analog of Contata's initial accept-all CATA). The
    hole's goal type is its *body* type (abstractions already peeled), so a base
    constant suffices. Returns ``None`` for non-base carriers (no obvious stub)."""
    from aeon.core.types import RefinedType, TypeConstructor, t_bool, t_float, t_int, t_string

    base = ty.type if isinstance(ty, RefinedType) else ty
    if isinstance(base, TypeConstructor):
        defaults = {
            t_int.name: (0, t_int),
            t_bool.name: (False, t_bool),
            t_float.name: (0.0, t_float),
            t_string.name: ("", t_string),
        }
        if base.name in defaults:
            value, vty = defaults[base.name]
            return Literal(value, vty)
    return None


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


def _joint_accepts(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    fills: dict[Name, Term],
    metadata: Metadata,
    constructor_names: set[str] | None = None,
) -> bool:
    """Contata Algorithm 2, lines 11-13: does the *joint* candidate assignment
    satisfy the spec? Fill every group hole, then require:
    (a) the whole program type checks (the relational/refinement oracle);
    (b) any ``@example`` assertions on the group's members all pass; and
    (c) any ``@property`` assertions hold under property-based testing — these
        are the **relational / k-safety** specifications over *several* functions
        or *several runs* of one function (e.g. ``even x == !(odd x)`` or
        ``reverse (reverse x) == x``) that cannot be a single function's
        refinement type (issue #397)."""
    filled = term
    for hole_name, cand in fills.items():
        filled = substitution(filled, cand, hole_name)
    if not check_type(ctx, filled, Top()):
        return False
    from aeon.synthesis.pbt.runner import run_examples, run_properties

    try:
        if not all(r.passed for r in run_examples(ectx, filled, metadata)):
            return False
        prop_results = run_properties(ctx, ectx, filled, metadata, constructor_names=constructor_names or set())
    except Exception:
        return False
    return all(r.passed for r in prop_results)


def _accumulate_trace(
    trace: list,
    observed: list,
    symbolic: list,
    seen_obs: set,
    seen_sym: set,
) -> None:
    """Fold an instrumented call trace into the observed-fact set ``θ`` and the
    symbolic tail-edges, using the recorded call-tree parents.

    Each entry is ``[name, args, result, parent_index]``. A call whose result
    equals its parent's was the parent's *tail call* (e.g. ``even(2) = odd(1)``),
    so we add the edge ``parent = child`` — and *only* genuine parent/child
    pairs, so unrelated calls that merely share a value (e.g. an eagerly
    evaluated ``@example`` binding) never forge a spurious edge that would
    over-constrain the SMT model. Calls whose result is still a function
    (multi-argument partial applications) are skipped."""
    for entry in trace:
        nm, a, res = entry[0], entry[1], entry[2]
        if callable(res):
            continue
        k = (nm.name, repr(a), repr(res))
        if k not in seen_obs:
            seen_obs.add(k)
            observed.append((nm, a, res))
    for i, entry in enumerate(trace):
        p = entry[3]
        if p < 0:
            continue
        nm_i, a_i, res_i = entry[0], entry[1], entry[2]
        nm_p, a_p, res_p = trace[p][0], trace[p][1], trace[p][2]
        if callable(res_i) or callable(res_p):
            continue
        if res_p == res_i and (nm_p.name, repr(a_p)) != (nm_i.name, repr(a_i)):
            key = (nm_p.name, repr(a_p), nm_i.name, repr(a_i))
            if key not in seen_sym:
                seen_sym.add(key)
                symbolic.append(((nm_p, a_p), (nm_i, a_i)))


def _contains_member(t: Term, names: set[str]) -> bool:
    """Does ``t`` mention any function under synthesis?"""
    match t:
        case Var(nm):
            return nm.name in names
        case Application(fun, arg):
            return _contains_member(fun, names) or _contains_member(arg, names)
        case Annotation(expr, _):
            return _contains_member(expr, names)
        case If(c, th, el):
            return _contains_member(c, names) or _contains_member(th, names) or _contains_member(el, names)
        case _:
            return False


def _find_top_level_def(core: Term, name_str: str) -> tuple[list[Name], Term] | None:
    """Return ``(value-param names, body)`` of a top-level binding, or ``None``."""
    cur: Term = core
    while isinstance(cur, Rec):
        if cur.var_name.name == name_str:
            val: Term = cur.var_value
            params: list[Name] = []
            while isinstance(val, Abstraction):
                params.append(val.var_name)
                val = val.body
            return params, val
        cur = cur.body
    return None


_REL_BINOPS = {"==", "!=", "&&", "||", "<", "<=", ">", ">="}


def _property_to_ir(body: Term, filled_core: Term, ectx: EvaluationContext, member_names: set[str]):
    """Translate a (counterexample-instantiated) property body into the relational
    IR consumed by :func:`_smt_unsat_core_obligations`.

    Sub-terms free of any function under synthesis are *evaluated* to concrete
    values (``("val", v)``); applications of a function under synthesis become
    symbolic ``("app", name, arg-values)`` nodes (their argument terms — already
    closed, since the property's parameter has been substituted — are evaluated
    in the program); boolean/relational operators are kept symbolic. Returns the
    IR, or ``None`` for an unsupported shape."""
    from aeon.backend.evaluator import eval as aeon_eval

    def ev(t: Term):
        return aeon_eval(set_program_tail(filled_core, t), ectx)

    def go(t: Term):
        if not _contains_member(t, member_names):
            return ("val", ev(t))
        # Peel the application spine, then strip type/refinement applications from
        # the head (a polymorphic operator like ``==`` appears as ``(==)[Bool]``).
        head: Term = t
        args: list[Term] = []
        while isinstance(head, Application):
            args.append(head.arg)
            head = head.fun
        args.reverse()
        while isinstance(head, (TypeApplication, RefinementApplication)):
            head = head.body
        if isinstance(head, Var):
            nm = head.name.name
            if nm in member_names:
                try:
                    return ("app", nm, tuple(ev(a) for a in args))
                except Exception:
                    return None
            if nm == "!" and len(args) == 1:
                inner = go(args[0])
                return ("not", inner) if inner is not None else None
            if nm in _REL_BINOPS and len(args) == 2:
                ia, ib = go(args[0]), go(args[1])
                return ("bin", nm, ia, ib) if ia is not None and ib is not None else None
        return None

    try:
        return go(body)
    except Exception:
        return None


def _member_apps_in_ir(ir, acc: set) -> None:
    """Collect every ``("app", name, args)`` (call to a function under synthesis)
    appearing in a relational IR."""
    if not isinstance(ir, tuple) or not ir:
        return
    if ir[0] == "app":
        acc.add((ir[1], ir[2]))
    elif ir[0] == "not":
        _member_apps_in_ir(ir[1], acc)
    elif ir[0] == "bin":
        _member_apps_in_ir(ir[2], acc)
        _member_apps_in_ir(ir[3], acc)


def _property_counterexamples(
    filled_core: Term, metadata: Metadata, ectx: EvaluationContext, member_names: set[str], max_input: int = 8
) -> tuple[list, set]:
    """Drive each ``@property`` over a small integer domain; for every input on
    which it *fails*, return its relational IR and the set of member calls it
    makes.

    A relational property (e.g. ``even n = !(odd n)``) is the only spec that sees
    a *deep* input. Its IR states the relation the unsat-core engine needs to
    detect the conflict, and re-running each of its member calls (separately, so
    each trace is a single recursion chain) exercises the recursion down to the
    example-anchored base cases — together letting the engine propagate
    obligations up the call chain (property-as-guide, not just filter).
    Properties with non-integer or multi-argument parameters are skipped."""
    from aeon.backend.evaluator import eval as aeon_eval
    from aeon.core.types import t_int

    prop_names = [
        key
        for key, entry in metadata.items()
        if isinstance(key, Name) and isinstance(entry, dict) and "property" in entry
    ]
    irs: list = []
    member_calls: set = set()
    for pn in prop_names:
        found = _find_top_level_def(filled_core, pn.name)
        if found is None or len(found[0]) != 1:
            continue  # need exactly one (integer) parameter to drive
        (param,), body = found
        for v in range(0, max_input + 1):
            call: Term = Application(Var(pn), Literal(v, t_int))
            try:
                result = aeon_eval(set_program_tail(filled_core, call), ectx)
            except Exception:
                break  # wrong arity / non-int param: this property isn't drivable here
            if result is False:
                ir = _property_to_ir(substitution(body, Literal(v, t_int), param), filled_core, ectx, member_names)
                if ir is not None:
                    irs.append(ir)
                    _member_apps_in_ir(ir, member_calls)
    return irs, member_calls


def _refine_obligations(
    filled_core: Term,
    members: list[tuple[Name, Name]],
    ectx: EvaluationContext,
    metadata: Metadata,
) -> int:
    """Contata's refinement phase (Algorithm 2, lines 11-16).

    Execute the current joint candidate (``filled_core``) under the instrumented
    semantics — on every member's I/O examples *and* on the failing inputs of any
    relational ``@property`` (property-as-guide) — then hand the ground spec
    ``ψ`` (``@example`` facts), the observed calls ``θ`` and the candidate's
    symbolic structure to z3. Its unsat core blames the conflicting calls and a
    model yields each blamed callee's spec-consistent output, added to that
    callee's ``io_examples``: the lazy refinement that constrains the callee's
    next-round search on exactly the input implicated by the conflict. Returns
    how many new obligations were added (0 ⇒ fixpoint). Only group members are
    refined."""
    from aeon.backend.evaluator import eval_with_trace

    member_name_strs = {fun_name.name for fun_name, _ in members}
    name_to_fun = {fun_name.name: fun_name for fun_name, _ in members}

    # ψ: the ground spec, as f(args)=out facts.
    spec_facts: list[tuple[Name, tuple, Any]] = []
    for fun_name, _hole in members:
        for args, out in metadata.get(fun_name, {}).get("io_examples", []):
            spec_facts.append((fun_name, tuple(args), out))

    # θ + structure: from running the candidate on every example input, and on
    # each relational property's failing inputs.
    observed: list[tuple[Name, tuple, Any]] = []
    symbolic: list[tuple[tuple[Name, tuple], tuple[Name, tuple]]] = []
    seen_obs: set = set()
    seen_sym: set = set()
    for fun_name, _hole in members:
        for args, _out in metadata.get(fun_name, {}).get("io_examples", []):
            call: Term = Var(fun_name)
            ok = True
            for v in args:
                lit = _value_literal(v)
                if lit is None:
                    ok = False
                    break
                call = Application(call, lit)
            if not ok:
                continue
            try:
                _actual, trace = eval_with_trace(set_program_tail(filled_core, call), ectx)
            except Exception:
                continue
            _accumulate_trace(trace, observed, symbolic, seen_obs, seen_sym)

    relational, prop_member_calls = _property_counterexamples(filled_core, metadata, ectx, member_name_strs)
    # Re-run each member call the failing properties make, separately, so each
    # trace is a single recursion chain (no spurious cross-call structure edges).
    for fname_str, argvals in prop_member_calls:
        target = name_to_fun.get(fname_str)
        if target is None:
            continue
        call = Var(target)
        ok = True
        for v in argvals:
            lit = _value_literal(v)
            if lit is None:
                ok = False
                break
            call = Application(call, lit)
        if not ok:
            continue
        try:
            _actual, trace = eval_with_trace(set_program_tail(filled_core, call), ectx)
        except Exception:
            continue
        _accumulate_trace(trace, observed, symbolic, seen_obs, seen_sym)

    obligations = _smt_unsat_core_obligations(spec_facts, observed, symbolic, member_name_strs, relational=relational)

    added = 0
    for fname, args, out in obligations:
        target = name_to_fun.get(fname.name, fname)
        callee_examples = metadata.setdefault(target, {}).setdefault("io_examples", [])
        obligation = (list(args), out)
        if obligation not in callee_examples:
            callee_examples.append(obligation)
            added += 1
    return added


def _contata_version_space_group(
    members: list[tuple[Name, Name]],
    program_holes: dict[Name, tuple[Type, TypingContext]],
    metadata: Metadata,
    synthesizer: Synthesizer,
) -> Optional[dict[Name, Optional[Term]]]:
    """Try the ``contata`` version space over the whole mutual group, returning a
    ``{hole_name: body}`` assignment or ``None`` (wrong backend, unsupported
    member, or no solution). Pure synthesis — the caller still gates on
    :func:`_joint_accepts`."""
    from aeon.synthesis.modules.contata.synthesizer import (
        ContataSynthesizer,
        GroupMember,
        cosynthesize_group,
    )

    if not isinstance(synthesizer, ContataSynthesizer):
        return None
    gms: list[GroupMember] = []
    hole_of: dict[Name, Name] = {}
    for fun_name, hole_name in members:
        ty, tyctx = program_holes[hole_name]
        if not isinstance(tyctx, TypingContext):
            return None
        gms.append(GroupMember(fun_name, ty, tyctx, metadata.get(fun_name, {})))
        hole_of[fun_name] = hole_name
    bodies = cosynthesize_group(gms, gms[0].hole_ctx, max_size=synthesizer.max_size)
    if bodies is None:
        return None
    return {hole_of[fn]: body for fn, body in bodies.items()}


def _cosynthesize_group(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    group: list[tuple[Name, list[Name]]],
    program_holes: dict[Name, tuple[Type, TypingContext]],
    metadata: Metadata,
    synthesizer: Synthesizer,
    budget: float,
    ui: SynthesisUI,
    budget_eval: float,
    rounds: int = 3,
    constructor_names: set[str] | None = None,
) -> dict[Name, Optional[Term]]:
    """Co-synthesize a mutual group, following Contata's lazy synthesis
    (Algorithm 2): each round pops a candidate for *every* member (with its
    siblings filled by the round's current candidates) and then checks the
    *joint* assignment against the spec. The per-member candidate search plays
    the role of ``MinTree(Ω(f))``; ``validate`` (the liquid typechecker) and the
    ``@example`` runner together play the acceptance oracle. Re-search across
    rounds stands in for the paper's unsat-core CATA refinement (lines 14-16):
    once siblings are filled, a member's PBE/relational search is constrained by
    their concrete behaviour, so a failing joint check drives the next round
    toward a consistent assignment."""
    members = [(fun_name, holes[0]) for fun_name, holes in group]

    # Fast path: the genuine CATA version space. When the backend is ``contata``
    # and every member is a unary Int/Bool function with @example facts, discharge
    # the *whole group* in one SMT query — a member's body may call its siblings
    # (uninterpreted functions), so the assignment is mutually consistent by
    # construction. This converges on the MR flagship (even/odd from examples)
    # that the per-member sibling-as-typed-oracle loop below cannot.
    vs = _contata_version_space_group(members, program_holes, metadata, synthesizer)
    if vs is not None and _joint_accepts(ctx, ectx, term, vs, metadata, constructor_names):
        return vs

    # Initialise each sibling to a trivial stub (the executable analog of the
    # accept-all CATA): keeps example evaluation total during the first round.
    fills: dict[Name, Optional[Term]] = {h: _trivial_stub(program_holes[h][0]) for _, h in members}
    # Track which fills are real (synthesised) vs. stubs, so the joint check only
    # accepts a fully-synthesised assignment.
    synthesised: set[Name] = set()
    per_budget = max(budget / max(rounds * len(members), 1), 1.0)

    for _round in range(rounds):
        for fun_name, hole_name in members:
            # Fill the *other* members with their current candidates so this
            # member is synthesised against concrete callees.
            prog = term
            for other_hole, cand in fills.items():
                if other_hole != hole_name and cand is not None:
                    prog = substitution(prog, cand, other_hole)
            ty, tyctx = program_holes[hole_name]
            assert isinstance(tyctx, TypingContext)
            try:
                fills[hole_name] = _synthesize_one(
                    ctx, ectx, prog, fun_name, hole_name, ty, tyctx, metadata, synthesizer, per_budget, ui, budget_eval
                )
                synthesised.add(hole_name)
            except Exception:
                synthesised.discard(hole_name)
        # Joint acceptance check: only when every member is genuinely synthesised
        # (no stubs left), and the joint assignment satisfies the spec.
        if synthesised == {h for _, h in members}:
            chosen = {h: fills[h] for _, h in members}
            if all(c is not None for c in chosen.values()) and _joint_accepts(
                ctx, ectx, term, chosen, metadata, constructor_names
            ):
                return dict(fills)
        # Refinement phase (Algorithm 2, lines 11-16): blame the failing examples'
        # tail-callees and grow their per-function obligations, so the next round
        # searches each member under the inputs implicated by the conflict.
        filled = term
        for h, cand in fills.items():
            if cand is not None:
                filled = substitution(filled, cand, h)
        _refine_obligations(filled, members, ectx, metadata)
    # No jointly-valid assignment found: return only genuinely-synthesised members
    # (stubs are not solutions), so the caller leaves the rest as holes.
    return {h: (fills[h] if h in synthesised else None) for _, h in members}


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
