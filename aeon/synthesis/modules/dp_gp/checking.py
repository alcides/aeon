"""Explicit transformation obligations; finite key checks are not universal proofs."""

from dataclasses import replace
from time import monotonic

import z3

from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.modules.dp_gp.model import dominates, execute, nodes


def symbolic_relation(modes, a, b):
    return z3.And(
        *[x == y if mode == 1 else x >= y if mode == 2 else x <= y for mode, x, y in zip(modes, a, b) if mode]
    )


def counterexample(formula, variables, deadline):
    solver = z3.Solver()
    solver.set(timeout=max(1, min(1000, int((deadline - monotonic()) * 1000))))
    solver.add(formula)
    answer = solver.check()
    if answer == z3.unknown:
        raise SynthesisNotSuccessful("dp_gp transformation obligation is unknown or timed out")
    if answer == z3.unsat:
        return None
    return tuple(solver.model().eval(v, model_completion=True).as_long() for v in variables)


def relation_counterexample(problem, modes, deadline):
    a = z3.Ints("a0 a1 a2")
    b = z3.Ints("b0 b1 b2")
    d = z3.Ints("d0 d1 d2")
    # Both objective compatibility and preservation through ANY legal additive
    # extension, not just current sampled objective comparisons.
    relation = symbolic_relation(modes, a, b)
    bad = z3.Or(
        problem.score.symbolic(a) < problem.score.symbolic(b),
        z3.Not(symbolic_relation(modes, [x + y for x, y in zip(a, d)], [x + y for x, y in zip(b, d)])),
    )
    return counterexample(z3.And(relation, bad), (*a, *b, *d), deadline)


def representation_counterexample(problem, plan, deadline):
    if len(plan.updates) != len(plan.solution_fields):
        return ("malformed_updates",)
    required = problem.score.variables() | {i for i, mode in enumerate(plan.relation) if mode}
    if not required <= set(plan.solution_fields) or not plan.solution_fields:
        return ("missing_query", tuple(sorted(required)))
    x, y = z3.Ints("old delta")
    for index, update in enumerate(plan.updates):
        found = counterexample(update.symbolic((x, y)) != x + y, (x, y), deadline)
        if found is not None:
            return ("update", index, found)
    return None


def state_requirements(problem, plan):
    needed = problem.allow.variables() | set(plan.key_fields)
    for index in plan.solution_fields:
        needed |= problem.delta[index].variables()
    for index in plan.state_fields:
        needed |= problem.step[index].variables()
    return needed - {3}  # action is supplied, not stored


def key_counterexample(roots, problem, plan, meter):
    for case, root in enumerate(roots):
        cache = {}
        for node in nodes(root):
            meter.tick()
            # Compare complete represented frontiers, never just their optima.
            result, _ = execute(problem, node, replace(plan, key_fields=(0, 1, 2)), memoize=False)
            projected = tuple(sorted(set(tuple(p[i] for i in plan.solution_fields) for p in result)))
            key = (node.fuel, tuple(node.state[i] for i in plan.key_fields))
            if key in cache and cache[key][1] != projected:
                return (case, cache[key][0], node.state, node.fuel)
            cache[key] = (node.state, projected)
    return None


def relation_loss(problem, modes, cases):
    return sum(dominates(modes, a, b) and problem.score.run(a) < problem.score.run(b) for a, b in cases)
