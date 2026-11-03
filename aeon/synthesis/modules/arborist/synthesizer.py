"""Aeon adapter for Arborist-style lifted interpretation of local holes."""

from __future__ import annotations

from time import monotonic
from typing import Optional

from loguru import logger

from aeon.backend.evaluator import EvaluationContext, eval as evaluate
from aeon.core.terms import Let, Rec, Term, Var
from aeon.core.types import Type, refined_to_unrefined_type, t_bool, t_int, top
from aeon.decorators.api import Metadata
from aeon.synthesis.api import ProgramSynthesizer, SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.candidate_archive import CandidateArchive
from aeon.synthesis.decorators import Goal
from aeon.synthesis.evaluation_pool import EvaluationPool, OK
from aeon.synthesis.example_adapters import adapt_example_metadata
from aeon.synthesis.fitness_eval import make_bundled_fitness_evaluator, set_program_tail, without_main_placeholder
from aeon.synthesis.pbt.runner import make_property_fitness, property_corpora_for_target
from aeon.synthesis.specifications import CHECKABLE_GOALS, checked_validator
from aeon.synthesis.identification import get_holes, get_holes_info
from aeon.synthesis.modules.arborist.forest import Forest, SearchStats, scalar_key, scalar_labels
from aeon.synthesis.modules.arborist.interpreter import LiftedInterpreter
from aeon.synthesis.modules.bottom_up import safe
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


class ArboristSynthesizer(ProgramSynthesizer):
    """Search one scalar expression hole inside a pure functional sketch.

    Program-level access is necessary: the enclosing lambda applications and
    recursive combinators determine local contexts, including candidate-dependent
    accumulators. Only inspecting the hole's typing context would lose them.
    """

    supports_optimization = False
    supports_candidate_enumeration = True

    def __init__(
        self,
        max_depth: int = 3,
        *,
        constants: tuple[int, ...] = (0, 1, 2),
        operators: tuple[str, ...] = ("+", "-", "*", "==", "<", "<=", "&&", "||", "!"),
        conditionals: bool = True,
        compress: bool = True,
        max_states: int = 100_000,
        max_steps: int = 1_000_000,
    ):
        if max_depth < 0 or max_states <= 0 or max_steps <= 0:
            raise ValueError("arborist requires nonnegative depth and positive resource limits")
        self.max_depth = max_depth
        self.constants = constants
        self.operators = operators
        self.conditionals = conditionals
        self.compress = compress
        self.max_states = max_states
        self.max_steps = max_steps
        self.stats = SearchStats()
        self.reachable: set[tuple] = set()

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
        from aeon.synthesis.entrypoint import _ectx_for_workers, _pool_backed, make_program, make_validator

        start = monotonic()
        deadline = start + budget
        program = without_main_placeholder(term)
        if len(targets) != 1 or len(targets[0][1]) != 1 or len(get_holes(program)) != 1:
            raise UnsupportedSynthesisGoal("arborist requires one expression hole in one function")
        function, holes = targets[0]
        hole = holes[0]
        corpora = property_corpora_for_target(ctx, program, metadata, function, {function}, evaluation_ctx=ectx)
        entry = adapt_example_metadata(
            ctx,
            _ectx_for_workers(ectx),
            program,
            function,
            metadata.get(function, {}),
            corpora,
            hole_name=hole,
            budget=min(2.0, max(0.0, budget / 5)),
        )
        # Prefer tagged constructors over the legacy flattened-list I/O encoding.
        rows = entry.get("constructor_io_examples") or entry.get("io_examples", [])
        if not rows:
            raise UnsupportedSynthesisGoal(
                "arborist requires literal scalar/constructor @example inputs and Int/Bool outputs"
            )
        # General assertions stay runtime checks; derived/CSV observations can
        # guide the packed interpreter alongside literal @example rows.
        for inputs, output in rows:
            scalar_key(output)

        ty, hole_ctx = get_holes_info(ctx, program, top, targets, refined_types=True)[hole]
        result_type = refined_to_unrefined_type(ty)
        if result_type not in (t_int, t_bool):
            raise UnsupportedSynthesisGoal("arborist requires an Int or Bool expression hole")
        definitions: dict[Name, Term] = {}
        current = program
        while isinstance(current, (Let, Rec)):
            definitions[current.var_name] = current.var_value
            if current.var_name == function:
                break
            current = current.body
        if function not in definitions:
            raise UnsupportedSynthesisGoal("arborist requires a top-level target function")

        # Only lexical parameters/locals belong to a hole's context signature.
        # Global operators are grammar labels, and pure helper functions are
        # interpreted from their Core definitions in the surrounding sketch.
        local_names: set[Name] = set()
        past_function = False
        for name, _ in hole_ctx.vars():
            if past_function:
                local_names.add(name)
            if name == function:
                past_function = True
        variables: list[tuple[Name, Type]] = []
        available = set()
        for name, variable_type in hole_ctx.concrete_vars():
            available.add(name)
            base = refined_to_unrefined_type(variable_type)
            if name in local_names and base in (t_int, t_bool):
                variables.append((name, base))
        forest = Forest(
            scalar_labels(
                variables, available, constants=self.constants, operators=self.operators, conditionals=self.conditionals
            ),
            deadline,
            compress=self.compress,
            max_states=self.max_states,
        )
        interpreter = LiftedInterpreter(forest, definitions, hole, max_steps=self.max_steps)
        for inputs, _ in rows:
            for argument in inputs:
                interpreter.check_data(argument)
        self.stats = forest.stats
        self.reachable = interpreter.reachable
        replace = make_program(program, hole)
        validate = make_validator(ctx, replace)

        def runtime_check(filled: Term) -> bool:
            fun = evaluate(set_program_tail(filled, Var(function)), ectx)
            for inputs, expected in rows:
                value = fun
                for argument in inputs:
                    value = value(argument)
                if scalar_key(value) != scalar_key(expected):
                    return False
            return True

        workers_ctx = _ectx_for_workers(ectx)
        properties = [make_property_fitness(corpus, workers_ctx, target=function) for corpus in corpora]
        goals = list(entry.get("goals", [])) + [Goal(True, 1, corpus.spec.name, "property") for corpus in corpora]
        local_metadata = dict(metadata) | {function: dict(entry) | {"goals": goals}}
        checks = [g for g in goals if g.kind in CHECKABLE_GOALS]
        computations = {
            "examples": runtime_check,
            "fitness": make_bundled_fitness_evaluator(goals, workers_ctx, function, program, properties),
        }
        if checks:
            computations["specification"] = make_bundled_fitness_evaluator(
                checks, workers_ctx, function, program, properties
            )
        pool = EvaluationPool(replace, computations, budget_eval=max(0.01, min(1.0, budget)))
        if checks:
            validate = checked_validator(validate, pool)
        fitness, _ = _pool_backed(pool)
        archive = CandidateArchive(self, function, local_metadata, fitness, max(0.0, deadline - monotonic()), ui)
        ui.start(hole_ctx, ectx, hole.pretty(), ty, budget)
        ui.register(None, None, 0, True)
        try:
            for depth in range(self.max_depth + 1):
                language = forest.grammar(result_type, depth)
                consistent = True
                for inputs, expected in rows:
                    survivors = [
                        state
                        for output, state in interpreter.run(function, inputs, language)
                        if scalar_key(output) == scalar_key(expected)
                    ]
                    if not survivors:
                        consistent = False
                        break
                    language = forest.union(survivors)
                if not consistent:
                    continue
                for candidate in forest.terms(language):
                    forest.check_budget()
                    self.stats.validated += 1
                    if not safe(validate, candidate):
                        continue
                    forest.check_budget()
                    status, accepted = pool.run(candidate).get("examples", ("error", False))
                    if status != OK or accepted is not True:
                        continue
                    if not archive.consider(candidate):
                        continue
                    elapsed = monotonic() - start
                    ui.register(candidate, [0.0] * len(rows), elapsed, True)
                    ui.end(candidate, [0.0] * len(rows))
                    logger.log(
                        "SYNTHESIZER",
                        f"arborist: {len(forest.states)} packed states, {self.stats.transitions} transitions, {self.stats.merges} merges, {len(self.reachable)} reachable contexts, {self.stats.validated} extracted candidates checked",
                    )
                    return {hole: candidate}
                ui.progress(self.stats.transitions, self.stats.validated, monotonic() - start)
            selected = archive.result()
            if selected is not None:
                ui.end(selected, None)
                return {hole: selected}
            raise SynthesisNotSuccessful(
                f"arborist: no validated example-consistent expression through depth {self.max_depth}"
            )
        except RecursionError as exc:
            ui.end(None, None)
            raise SynthesisNotSuccessful("arborist interpreter recursion limit exhausted") from exc
        except UnsupportedSynthesisGoal:
            raise
        except SynthesisNotSuccessful:
            selected = archive.result()
            ui.end(selected, None)
            if selected is not None:
                return {hole: selected}
            raise
        except Exception:
            ui.end(None, None)
            raise
        finally:
            pool.close()
