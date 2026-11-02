"""Source-level DP transformations with GP components and a bounded oracle."""

from dataclasses import asdict
from itertools import product
import random
from time import monotonic

from aeon.backend.evaluator import eval as evaluate
from aeon.core.terms import Hole, Var
from aeon.core.types import top
from aeon.synthesis.api import ProgramSynthesizer, SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.fitness_eval import set_program_tail, without_main_placeholder
from aeon.synthesis.identification import get_holes, get_holes_info, iterate_top_level
from aeon.synthesis.modules.dp_gp.emission import Emitter, apply, integer
from aeon.synthesis.modules.dp_gp.model import Config, Meter, optimum, trace
from aeon.synthesis.modules.dp_gp.search import search
from aeon.synthesis.modules.dp_gp.source import problem_from_source, unpack
from aeon.synthesis.modules.noisy.worker import Worker, WorkerError, WorkerTimeout


class DPSynthesizer(ProgramSynthesizer):
    def __init__(self, seed=0, config=None):
        self.config = config or Config.from_env(seed)
        self.seed = self.config.seed
        self.last_report = None

    def synthesize_program(self, ctx, ectx, term, targets, metadata, budget=60, ui=None):
        from aeon.synthesis.entrypoint import make_program, make_validator
        from aeon.synthesis.uis.api import SynthesisUI

        ui = ui or SynthesisUI()
        self.last_report = None
        started = monotonic()
        deadline = started + max(0, budget)
        program = without_main_placeholder(term)
        if len(targets) != 1 or len(targets[0][1]) != 1 or len(get_holes(program)) != 1:
            raise UnsupportedSynthesisGoal("dp_gp requires one top-level scalar body hole")
        function, holes = targets[0]
        hole = holes[0]
        entry = metadata.get(function, {})
        declaration = entry.get("dp_gp")
        if declaration is None:
            raise UnsupportedSynthesisGoal("dp_gp requires @dp_gp(reference, max_first_input, max_second_input)")
        for data in metadata.values():
            if isinstance(data, dict) and any(data.get(k) for k in ("goals", "property", "cluster", "recursion")):
                raise UnsupportedSynthesisGoal(
                    "dp_gp uses the reference objective; extra goals/properties are unsupported"
                )
        reference_name, *bounds = declaration
        if bounds[0] > self.config.max_fuel or (bounds[0] + 1) * (bounds[1] + 1) > self.config.max_instances:
            raise UnsupportedSynthesisGoal("dp_gp declared input domain exceeds configured exhaustive-check limits")
        ui.start(ctx, ectx, str(hole), None, budget)

        def work(_):
            meter = Meter(deadline, self.config.max_nodes)
            declarations = {d.var_name: d for d in iterate_top_level(program)}
            definitions = {n: d.var_value for n, d in declarations.items()}
            references = [d for n, d in declarations.items() if n.name == reference_name]
            if len(references) != 1:
                raise UnsupportedSynthesisGoal("dp_gp reference must name one preceding definition")
            reference = references[0]
            target = declarations[function]
            params, body = unpack(target, bounds, deadline, target=True)
            if not isinstance(body, Hole) or body.name != hole:
                raise UnsupportedSynthesisGoal("dp_gp target must have a single unnested body hole")
            problem = problem_from_source(reference, tuple(bounds), definitions, deadline)
            _, hole_ctx = get_holes_info(ctx, program, top, targets, refined_types=True)[hole]
            names = {}
            for key, suffix in (
                ("vnil", "DPVector_vnil"),
                ("cell", "DPVector_cell"),
                ("get", "DP_get"),
                ("solve", "DP_solve"),
            ):
                found = [n for n in definitions if n.name == suffix]
                if len(found) != 1:
                    raise UnsupportedSynthesisGoal("dp_gp requires the standard DP library")
                names[key] = found[0]
            vector_type = declarations[names["vnil"]].var_type
            # Constructor types include singleton refinements; component inputs
            # and outputs are arbitrary vectors.
            from aeon.core.types import refined_to_unrefined_type

            emitter = Emitter(names, refined_to_unrefined_type(vector_type))
            inputs = list(product(range(bounds[0] + 1), range(bounds[1] + 1)))
            roots = [trace(problem, values, meter) for values in inputs]
            if any(not root.solutions for root in roots):
                raise UnsupportedSynthesisGoal("dp_gp value-only contracts require a feasible solution on every input")
            if any(problem.score.run(p) < problem.floor for root in roots for p in root.solutions):
                raise UnsupportedSynthesisGoal("dp_gp floor must bound every feasible objective from below")
            # Preserve and execute the supplied Aeon reference as the oracle.
            for values, root in zip(inputs, roots):
                meter.tick()
                call = apply(Var(reference.var_name), *(integer(v) for v in values))
                actual = evaluate(set_program_tail(program, call), ectx)
                if type(actual) is not int or actual != optimum(problem, root.solutions):
                    raise SynthesisNotSuccessful("dp_gp IR disagrees with executable reference")
            indices = list(range(len(inputs)))
            random.Random(self.seed).shuffle(indices)
            split = max(1, len(inputs) // 4)
            train = sorted(indices[:split])
            held_out = sorted(indices[split : 2 * split])
            checking = sorted(indices[2 * split :])
            plan, stages, ablations = search(problem, roots, train, emitter, hole_ctx, self.config, meter, checking)
            candidate = emitter.algorithm(problem, plan, [Var(n) for n in params])
            replace = make_program(program, hole)
            if not make_validator(ctx, replace)(candidate):
                raise SynthesisNotSuccessful("dp_gp emitted algorithm failed whole-program refinement validation")
            completed = replace(candidate)
            for values, root in zip(inputs, roots):
                meter.tick()
                actual = evaluate(
                    set_program_tail(completed, apply(Var(function), *(integer(v) for v in values))), ectx
                )
                if type(actual) is not int or actual != optimum(problem, root.solutions):
                    raise SynthesisNotSuccessful("dp_gp emitted algorithm disagrees with reference")
            report = {
                "backend": "dp_gp",
                "assurance": "exhaustive on declared finite input domain",
                "universal_obligations": [
                    "preorder form",
                    "objective compatibility",
                    "additive extension",
                    "solution update",
                    "state projection and transition commutation",
                ],
                "bounded_obligations": ["memoization interchangeability", "emitted/reference equivalence"],
                "seed": self.seed,
                "config": asdict(self.config),
                "instances": inputs,
                "training_indices": train,
                "checking_indices": checking,
                "held_out_indices": held_out,
                "plan": asdict(plan),
                "stages": stages,
                "ablations": ablations,
                "checked_instances": len(inputs),
                "work": meter.nodes,
                "stop_reason": "completed",
                "elapsed_seconds": monotonic() - started,
            }
            return candidate, report

        worker = Worker({"synthesize": work})
        try:
            candidate, report = worker.call("synthesize", None, deadline - monotonic())
            self.last_report = report
            ui.register(candidate, [], monotonic() - started, True)
            ui.report(report)
            ui.end(candidate, [])
            return {hole: candidate}
        except (WorkerTimeout, WorkerError) as exc:
            ui.end(None, None)
            raise SynthesisNotSuccessful(f"dp_gp failed without a fully checked algorithm: {exc}") from exc
        finally:
            worker.close()
