"""Neural bounded Boolean synthesis: sample, learn gated CNF, verify, retrain.

Implements BNSynth's CNF architecture 1 (arXiv:2212.08170, Algorithm 1).
Z3 samples satisfying output tuples and verifies extracted programs; it never
chooses CNF gates. Sampling uses Aeon's compiler obligations rather than the
reference tool's Verilog/Manthan interface. All mutable state is per run.
"""

from dataclasses import dataclass
from math import isfinite
from random import Random
from time import monotonic

import z3

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Var
from aeon.core.types import t_bool
from aeon.synthesis.api import (
    InvalidIndividualException,
    SpecificationViolation,
    SynthesisNotSuccessful,
    TimeoutInEvaluationException,
    UnsupportedSynthesisGoal,
)
from aeon.synthesis.bounded_cnf import CNFResourceLimit, bounds, normalize
from aeon.synthesis.candidate_archive import CandidateArchive
from aeon.synthesis.joint import JointCandidate
from aeon.synthesis.modules.boolean_bounded import (
    BooleanBoundedSynthesizer,
    BooleanReport,
    BoundedBooleanFailure,
    _boolean_signature,
    _combine,
    _operator,
)
from aeon.synthesis.solver_problem import SolverProblem
from aeon.synthesis.uis.api import SynthesisUI


class BNSynthFailure(BoundedBooleanFailure):
    def __init__(self, category, message):
        self.category, self.message = category, message
        SynthesisNotSuccessful.__init__(self, f"bnsynth [{category}]: {message}")


@dataclass
class NeuralReport(BooleanReport):
    epochs: int = 0
    restarts: int = 0
    training_rows: int = 0
    trained_models: int = 0


class _Relation:
    """Universal compiler VCs and a finite, consistent table of training labels."""

    def __init__(self, problem, check, rng, remaining, max_nodes):
        self.problem, self.check, self.rng = problem, check, rng
        self.remaining, self.max_nodes = remaining, max_nodes
        self.nodes = 0
        self.functions = {
            h.symbol: z3.Function(f"bnsynth_{i}", *([z3.BoolSort()] * (len(h.params) + 1)))
            for i, h in enumerate(problem.holes)
        }
        self.indices = {f: i for i, f in enumerate(self.functions.values())}
        self.clauses = []
        for i, clause in enumerate(problem.clauses):
            if any(ty != t_bool for _, ty in clause.variables):
                raise UnsupportedSynthesisGoal("bnsynth requires Boolean verification variables")
            env = {n: z3.Bool(f"bnsynth_v{i}_{j}") for j, (n, _) in enumerate(clause.variables)}
            formula = z3.Implies(self.translate(clause.premise, env), self.translate(clause.conclusion, env))
            self.clauses.append((tuple(env.values()), formula))
        self.instances = []
        self.instance_keys = set()

    def translate(self, term, variables):
        self.nodes += 1
        self.remaining()
        if self.nodes > self.max_nodes:
            raise BNSynthFailure("resource_limit", "Boolean obligation size limit exceeded")
        if isinstance(term, LiquidLiteralBool):
            return z3.BoolVal(term.value)
        if isinstance(term, LiquidVar) and term.name in variables:
            return variables[term.name]
        if isinstance(term, LiquidApp):
            if term.fun in self.functions:
                fn = self.functions[term.fun]
                if fn.arity() == 0:
                    if term.args != [LiquidLiteralInt(0)]:
                        raise UnsupportedSynthesisGoal("invalid nullary unknown transport")
                    return fn()
                return fn(*[self.translate(a, variables) for a in term.args])
            operators = {
                "!": (1, z3.Not),
                "&&": (2, z3.And),
                "||": (2, z3.Or),
                "-->": (2, z3.Implies),
                "==": (2, lambda a, b: a == b),
                "!=": (2, lambda a, b: a != b),
                "ite": (3, z3.If),
            }
            entry = operators.get(term.fun.name) if term.fun.id == 0 else None
            if entry is not None and len(term.args) == entry[0]:
                return entry[1](*[self.translate(a, variables) for a in term.args])
        raise UnsupportedSynthesisGoal(f"bnsynth cannot translate Boolean predicate {term}")

    def add(self, index, model):
        variables, formula = self.clauses[index]
        instance = z3.simplify(z3.substitute(formula, [(v, model.eval(v, model_completion=True)) for v in variables]))
        key = instance.sexpr()
        if key in self.instance_keys or z3.is_true(instance):
            return
        # Drop genuine don't-care rows: every output tuple satisfies this row.
        solver = z3.Solver()
        solver.add(z3.Not(instance))
        if self.check(solver) == z3.unsat:
            return
        self.instances.append(instance)
        self.instance_keys.add(key)

    def sample(self, count):
        for index, (variables, formula) in enumerate(self.clauses):
            sampler = z3.Solver()
            sampler.set(random_seed=self.rng.randrange(2**31))
            # Find inputs at which the specification restricts some output.
            # Labels are subsequently drawn from the satisfying relation.
            sampler.add(z3.Not(formula))
            for _ in range(count):
                if self.check(sampler) == z3.unsat:
                    break
                model = sampler.model()
                self.add(index, model)
                sampler.add(z3.Or([v != model.eval(v, model_completion=True) for v in variables]))

    def labels(self):
        solver = z3.Solver()
        solver.set(random_seed=self.rng.randrange(2**31))
        solver.add(self.instances)
        if self.check(solver) == z3.unsat:
            # This is a conflicting finite specification, not failure to learn
            # a K-clause network. Never advertise neural failure as bounded UNSAT.
            raise BNSynthFailure("no_solution", "sampled obligations have no consistent Boolean outputs")
        apps = {}
        pending = list(self.instances)
        seen = set()
        while pending:
            self.remaining()
            term = pending.pop()
            if term.get_id() in seen:
                continue
            seen.add(term.get_id())
            if term.decl() in self.indices:
                apps[term.get_id()] = term
            pending.extend(term.children())
        # Choose one satisfying joint tuple for nondeterministic examples.
        # Preferences are local to this label draw; restarts may choose another.
        choices = list(apps.values())
        self.rng.shuffle(choices)
        for app in choices[:64]:
            preference = app == z3.BoolVal(bool(self.rng.getrandbits(1)))
            solver.push()
            solver.add(preference)
            status = self.check(solver)
            solver.pop()
            if status == z3.sat:
                solver.add(preference)
        assert self.check(solver) == z3.sat
        model = solver.model()
        data = [{} for _ in self.problem.holes]
        for app in apps.values():
            inputs = tuple(z3.is_true(model.eval(a, model_completion=True)) for a in app.children())
            value = z3.is_true(model.eval(app, model_completion=True))
            data[self.indices[app.decl()]][inputs] = value
        return data

    def verify(self, formulas):
        replacements = list(zip(self.functions.values(), formulas))
        violations = [z3.Not(z3.substitute_funs(formula, *replacements)) for _, formula in self.clauses]
        verifier = z3.Solver()
        verifier.add(z3.Or(violations))
        if self.check(verifier) == z3.unsat:
            return True
        model = verifier.model()
        index = next(
            i for i, violation in enumerate(violations) if z3.is_true(model.eval(violation, model_completion=True))
        )
        self.add(index, model)
        return False


class BNSynthSynthesizer(BooleanBoundedSynthesizer):
    supports_deterministic_budget = False
    deterministic_budget_limitation = "PyTorch training kernels are outside opcode accounting and depend on hardware."

    report_type = NeuralReport
    failure_type = BNSynthFailure

    def __init__(self, seed=0, *, initial_samples=8, epochs_per_restart=1000, max_selectors=100_000, max_nodes=100_000):
        super().__init__(seed, max_selectors=max_selectors, max_nodes=max_nodes)
        if initial_samples < 0 or epochs_per_restart < 1:
            raise ValueError("invalid BNSynth sampling/training limits")
        self.initial_samples = initial_samples
        self.epochs_per_restart = epochs_per_restart

    def _train(self, models, data, torch, remaining):
        for model, rows in zip(models, data):
            if not rows:
                continue
            inputs = torch.tensor(list(rows), dtype=torch.float64).reshape(len(rows), model.inputs)
            targets = torch.tensor(list(rows.values()), dtype=torch.float64)
            optimizer = torch.optim.Adam(model.parameters(), lr=0.01, weight_decay=0)
            self.report.trained_models += 1
            for _ in range(self.epochs_per_restart):
                remaining()
                if model.fits(inputs, targets):
                    break
                if model.bound == 0:
                    return False
                optimizer.zero_grad()
                loss = ((model(inputs) - targets) ** 2).mean() + model.regularization()
                if not bool(torch.isfinite(loss)):
                    raise BNSynthFailure("validation_error", "nonfinite neural training loss")
                loss.backward()
                optimizer.step()
                model.project()
                self.report.epochs += 1
            if not model.fits(inputs, targets):
                return False
        return True

    def synthesize_joint(self, holes, validate, evaluate, fun_name, metadata, budget=60, ui=SynthesisUI()):
        if not self._in_worker:
            return self.run_bounded(
                lambda remaining, worker_ui: self.synthesize_joint(
                    holes, validate, evaluate, fun_name, metadata, remaining, worker_ui
                ),
                budget,
                ui,
            )
        self.report = NeuralReport()
        start = monotonic()
        deadline = start + max(0, budget - min(0.05, budget * 0.05))

        def remaining():
            seconds = deadline - monotonic()
            if seconds <= 0:
                raise BNSynthFailure("timeout", "wall-clock budget exhausted")
            return seconds

        def check(solver):
            solver.set(timeout=max(1, int(remaining() * 1000)))
            self.report.solver_calls += 1
            result = solver.check()
            remaining()
            if result == z3.unknown:
                reason = solver.reason_unknown()
                raise BNSynthFailure("timeout" if "timeout" in reason or "canceled" in reason else "unknown", reason)
            return result

        def score(candidate):
            try:
                result = evaluate(candidate)
            except (InvalidIndividualException, TimeoutInEvaluationException) as exc:
                category = "timeout" if isinstance(exc, TimeoutInEvaluationException) else "validation_error"
                raise BNSynthFailure(category, "feasible candidate objective evaluation failed") from exc
            if not all(isfinite(value) for value in result):
                raise BNSynthFailure("validation_error", "objective returned a nonfinite score")
            return result

        archive = CandidateArchive(self, fun_name, metadata, score, budget, ui)
        try:
            try:
                import torch
                from aeon.synthesis.modules.bnsynth_model import GatedCNF
            except ImportError as exc:
                raise UnsupportedSynthesisGoal(
                    "bnsynth requires PyTorch: pip install 'AeonLang[synthesis-bnsynth]'"
                ) from exc
            # CPU training, with thread/RNG state confined to the worker.
            torch.set_num_threads(1)
            generator = torch.Generator(device="cpu").manual_seed(self.seed % (2**63))
            rng = Random(self.seed)
            remaining()
            problem = metadata.get(fun_name, {}).get("solver_problem")
            if not isinstance(problem, SolverProblem) or tuple(h.name for h in holes) != tuple(
                h.name for h in problem.holes
            ):
                raise UnsupportedSynthesisGoal("bnsynth requires the shared compiler solver problem")
            limits = bounds(metadata)
            ks = []
            for hole, schema in zip(holes, problem.holes):
                _boolean_signature(hole.type)
                if schema.base != t_bool or any(ty != t_bool for _, ty in schema.params):
                    raise UnsupportedSynthesisGoal("bnsynth requires Boolean inputs and outputs")
                k = limits.get(hole.function)
                if type(k) is not int or k < 0:
                    raise UnsupportedSynthesisGoal("every BNSynth target needs @bounded_cnf(K)")
                ks.append(k)
                self.report.selectors += k * (2 * len(schema.params) + 1)
            if self.report.selectors > self.max_selectors:
                raise BNSynthFailure("resource_limit", "neural gate limit exceeded")
            relation = _Relation(problem, check, rng, remaining, self.max_nodes)
            relation.sample(self.initial_samples)
            while True:
                remaining()
                self.report.iterations += 1
                data = relation.labels()
                self.report.training_rows = sum(map(len, data))
                models = [GatedCNF(len(h.params), k, generator) for h, k in zip(problem.holes, ks)]
                if not self._train(models, data, torch, remaining):
                    self.report.restarts += 1
                    continue
                formulas, terms = [], []
                for schema, model in zip(problem.holes, models):
                    clauses = model.clauses()
                    variables = [z3.Var(i, z3.BoolSort()) for i in range(len(schema.params))]
                    formulas.append(
                        z3.And(
                            [
                                z3.Or([variables[abs(v) - 1] if v > 0 else z3.Not(variables[abs(v) - 1]) for v in c])
                                for c in clauses
                            ]
                        )
                    )

                    def literal(v):
                        term = Var(schema.params[abs(v) - 1][0])
                        return term if v > 0 else _operator("!", term)

                    body = _combine("&&", [_combine("||", [literal(v) for v in c], False) for c in clauses], True)
                    if len(normalize(body, {n for n, _ in schema.params})) > model.bound:
                        raise BNSynthFailure("validation_error", "extracted network exceeds its CNF bound")
                    terms.append(schema.wrap(body))
                if not relation.verify(formulas):
                    self.report.counterexamples += 1
                    continue
                candidate = JointCandidate(tuple(terms))
                try:
                    valid = validate(candidate)
                except SpecificationViolation:
                    self.report.rejected_candidates += 1
                    self.report.restarts += 1
                    continue
                if not valid:
                    raise BNSynthFailure("validation_error", "neural candidate failed full Aeon/CNF validation")
                self.report.validated_candidates += 1
                remaining()
                if archive.consider(candidate):
                    self.report.status = "solved"
                    return candidate
                self.report.restarts += 1
        except BoundedBooleanFailure as exc:
            if exc.category == "timeout":
                incumbent = archive.result()
                if isinstance(incumbent, JointCandidate):
                    self.report.status = "budget"
                    return incumbent
            self.report.status = exc.category
            raise
        except UnsupportedSynthesisGoal:
            self.report.status = "unsupported"
            raise
        except TimeoutInEvaluationException as exc:
            self.report.status = "timeout"
            raise BNSynthFailure("timeout", "runtime validation timed out") from exc
        except (RecursionError, MemoryError, CNFResourceLimit) as exc:
            self.report.status = "resource_limit"
            raise BNSynthFailure("resource_limit", "neural synthesis resource limit exceeded") from exc
        except Exception as exc:
            self.report.status = "validation_error"
            raise BNSynthFailure("validation_error", f"{type(exc).__name__}: {exc}") from exc
        finally:
            self.report.elapsed = monotonic() - start
