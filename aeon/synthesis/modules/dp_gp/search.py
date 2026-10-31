"""Staged native GP with fresh fitness epochs and explicit acceptance gates."""

from dataclasses import asdict, replace
from itertools import product
from time import monotonic

from aeon.core.terms import Annotation, Let
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.modules.dp_gp.checking import (
    key_counterexample,
    relation_counterexample,
    relation_loss,
    representation_counterexample,
    state_requirements,
)
from aeon.synthesis.modules.dp_gp.emission import UPDATES
from aeon.synthesis.modules.dp_gp.model import Plan, execute, nodes, optimum
from aeon.synthesis.modules.genetic_programming import GeneticProgrammingSynthesizer
from aeon.synthesis.modules.tdsyn.worklist import PartialAST
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name, fresh_counter


def fields(gene):
    return tuple(i for i in range(3) if (gene % 8) & (1 << i))


def search(problem, roots, train_indices, emitter, ctx, config, meter, checking_indices=None):
    plan = Plan(updates=(UPDATES[4],) * 3)
    stages = []
    training = [roots[i] for i in train_indices]
    checking = roots if checking_indices is None else [roots[i] for i in checking_indices]
    relation_cases = []
    for root in training:
        for node in nodes(root):
            # Cap only initial training; the SMT gate covers all scalar values.
            relation_cases.extend(list(product(node.solutions[:8], repeat=2)))

    def evolve(stage, decode_plan, component, loss, gate, cost):
        nonlocal plan
        stats = {"stage": stage, "assessed": 0, "generations": 0, "counterexamples": [], "epochs": 0}
        rejected = set()
        for epoch in range(config.epochs):
            stats["epochs"] += 1
            candidates = {}
            valid_types = {}
            fitness = {}
            accepted = []

            def decode(genome, generation):
                meter.tick()
                stats["assessed"] += 1
                stats["generations"] = max(stats["generations"], generation)
                proposal = decode_plan(genome)
                term, ty = component(proposal)
                candidates[id(term)] = (proposal, ty)
                return term

            def validate(term):
                proposal, ty = candidates[id(term)]
                if proposal not in valid_types:
                    valid_types[proposal] = check_type(ctx, term, ty)
                return valid_types[proposal]

            def evaluate(term):
                proposal, _ = candidates[id(term)]
                if proposal in fitness:
                    return fitness[proposal]
                errors = loss(proposal) + int(proposal in rejected)
                work = cost(proposal)
                # Every correctness error dominates the normalized cost.
                if errors == 0:
                    accepted.append((work, repr(proposal), proposal))
                fitness[proposal] = [float(errors) + work / (1.0 + work)]
                return fitness[proposal]

            GeneticProgrammingSynthesizer(config.seed + 101 * len(stages) + epoch).search_components(
                PartialAST(emitter.vector([]), [], 0),
                decode,
                validate,
                evaluate,
                max(0, meter.deadline - monotonic()),
                config.proposals,
            )
            if not accepted:
                continue
            # Verify each distinct sample-admissible proposal in fitness order.
            # A newly discovered counterexample starts a fresh GP fitness epoch.
            proposal = min(accepted, key=lambda x: x[:2])[2]
            failure = gate(proposal)
            if failure is None:
                plan = proposal
                stats["status"] = "accepted"
                stats["plan"] = repr(plan)
                stages.append(stats)
                return
            rejected.add(proposal)
            stats["counterexamples"].append(failure)
        raise SynthesisNotSuccessful(f"dp_gp {stage}: no admissible component after {config.epochs} epochs")

    def relation_gate(p):
        found = relation_counterexample(problem, p.relation, meter.deadline)
        if found is not None:
            relation_cases.append((found[:3], found[3:6]))
        return found

    evolve(
        "thinning",
        lambda g: replace(plan, relation=tuple(g[i % len(g)] % 4 for i in range(3))),
        emitter.relation,
        lambda p: relation_loss(problem, p.relation, relation_cases),
        relation_gate,
        lambda p: sum(execute(problem, r, p, memoize=False)[1].retained for r in training),
    )

    update_cases = [(0, 0), (1, 0)]

    def representation(g):
        selected = fields(g[0])
        return replace(
            plan, solution_fields=selected, updates=tuple(UPDATES[g[(i + 1) % len(g)] % len(UPDATES)] for i in selected)
        )

    def representation_component(p):
        term, ty = emitter.projection(p.solution_fields)
        for update in p.updates:
            body, body_type = emitter.update(update)
            term = Let(Name("update", fresh_counter.fresh()), Annotation(body, body_type), term)
        return term, ty

    def rep_loss(p):
        required = problem.score.variables() | {i for i, mode in enumerate(p.relation) if mode}
        return (
            len(required - set(p.solution_fields))
            + int(not p.solution_fields)
            + sum(u.run((x, y)) != x + y for u in p.updates for x, y in update_cases)
        )

    def rep_gate(p):
        failure = representation_counterexample(problem, p, meter.deadline)
        if failure and failure[0] == "update":
            update_cases.append(failure[2])
        return failure

    evolve(
        "solution_representation",
        representation,
        representation_component,
        rep_loss,
        rep_gate,
        lambda p: len(p.solution_fields),
    )

    key_cases = list(training)

    def key_gate(p):
        failure = key_counterexample(checking, problem, p, meter)
        if failure:
            key_cases.append(checking[failure[0]])
        return failure

    evolve(
        "memoization_key",
        lambda g: replace(plan, key_fields=fields(g[0])),
        lambda p: emitter.projection(p.key_fields),
        lambda p: int(key_counterexample(key_cases, problem, p, meter) is not None),
        key_gate,
        lambda p: sum(len({(n.fuel, tuple(n.state[i] for i in p.key_fields)) for n in nodes(r)}) for r in training),
    )

    evolve(
        "state_representation",
        lambda g: replace(plan, state_fields=fields(g[0])),
        lambda p: emitter.projection(p.state_fields),
        lambda p: len(state_requirements(problem, p) - set(p.state_fields)) + int(not p.state_fields),
        lambda p: None if state_requirements(problem, p) <= set(p.state_fields) else "missing transition/query",
        lambda p: len(p.state_fields),
    )

    # Held-out states participate only in final acceptance, never GP feedback.
    if key_counterexample(roots, problem, plan, meter) is not None:
        raise SynthesisNotSuccessful("dp_gp memoization collision on final held-out validation")
    ablations = []
    for index, root in enumerate(roots):
        row = {"instance": index, "reference_value": optimum(problem, root.solutions)}
        for mode, selected, memo in (
            ("reference", None, False),
            ("thinning", replace(plan, solution_fields=(0, 1, 2), state_fields=(0, 1, 2)), False),
            ("full", plan, True),
        ):
            values, counts = execute(problem, root, selected, memo)
            actual = optimum(problem, values)
            if actual != row["reference_value"]:
                raise SynthesisNotSuccessful("dp_gp composed transformation changed the reference optimum")
            row[mode] = asdict(counts)
        ablations.append(row)
    return plan, stages, ablations
