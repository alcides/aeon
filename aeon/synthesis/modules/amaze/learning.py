"""Measured stdlib reconstructions, rank regression and additions-only search."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import math
from time import monotonic

from aeon.typechecking.typeinfer import check_type
from .core import equivalent, wrap
from .corpus import CorpusError, collect
from .grammar import Grammar, base_productions, evaluate, FEATURE_VERSION, GRAMMAR_VERSION
from .mining import mine, production


@dataclass(frozen=True)
class Config:
    seed: int = 0
    budget: float = 120.0
    task_budget: float = 2.0
    max_candidates: int = 20_000
    max_cost: int = 9
    iterations: int = 4
    max_macros: int = 4
    min_support: int = 2
    max_patterns: int = 32

    def __post_init__(self):
        if (
            not math.isfinite(self.budget)
            or not math.isfinite(self.task_budget)
            or self.budget <= 0
            or self.task_budget <= 0
            or not 1 <= self.max_candidates <= 1_000_000
        ):
            raise ValueError("positive budgets and 1..1000000 candidates required")
        if not 1 <= self.max_cost <= 15 or not 1 <= self.iterations <= 20 or not 1 <= self.max_macros <= 16:
            raise ValueError("cost/iteration/production limits out of range")
        if not 1 <= self.min_support <= 100 or not 1 <= self.max_patterns <= 128:
            raise ValueError("pattern limits out of range")


def reconstruct(task, macros, config, deadline):
    grammar = Grammar(base_productions(task.inputs) + tuple(macros))
    start = monotonic()
    stop = min(deadline, start + config.task_budget)
    record = {
        "task": task.id,
        "split": task.split,
        "source_sha256": task.source_hash,
        "productions": [p.id for p in macros],
        "status": "exhausted",
        "candidates": 0,
        "validation_failures": 0,
        "verification_unknown": 0,
        "reference_rank_bound": grammar.estimate(task.reference),
    }
    solution = None
    for expr, cost, used in grammar.enumerate(task.reference.sort, config.max_cost, config.max_candidates, stop):
        record["candidates"] += 1
        if any(evaluate(expr, args) != out for args, out in task.examples):
            continue
        # Probes cannot turn a weak return type into a reconstruction proof.
        verdict = equivalent(expr, task.reference, task.inputs, min(200, max(1, int((stop - monotonic()) * 1000))))
        if verdict != "equivalent":
            record["verification_unknown" if verdict == "unknown" else "validation_failures"] += 1
            continue
        with task.session.activate():
            valid = check_type(task.ctx, wrap(expr, task.variables), task.type)
        if not valid:
            record["validation_failures"] += 1
            continue
        record.update(
            status="solved",
            cost=cost,
            rank_bound=grammar.rank_bound(expr.sort, cost),
            used_macros=sorted(set(used) & {p.id for p in macros}),
            solution=expr.data(),
        )
        solution = expr
        break
    if solution is None:
        if monotonic() >= stop:
            record["status"] = "timeout"
        elif record["candidates"] >= config.max_candidates:
            record["status"] = "candidate_limit"
    record["elapsed"] = monotonic() - start
    record["censored"] = solution is None
    return record, solution


@dataclass(frozen=True)
class Model:
    intercept: float
    slope: float
    ridge: float
    target: str

    def predict(self, rank):
        return math.exp(min(50, self.intercept + self.slope * math.log1p(rank)))


def fit(labels, *, target="candidates", ridge=1.0):
    # Successful runs give exact measured costs; timeouts/limits only give
    # lower bounds. Censored rows incur loss ONLY below their observed cost.
    rows = [r for r in labels if r.get("rank_bound", r.get("reference_rank_bound")) is not None and r[target] > 0]
    if len(rows) < 2 or not any(r["status"] == "solved" for r in rows):
        raise CorpusError(
            "need stdlib measurements and at least one successful reconstruction; increase offline budgets"
        )
    xs = [math.log1p(r.get("rank_bound", r.get("reference_rank_bound"))) for r in rows]
    ys = [math.log(max(1e-9, r[target])) for r in rows]
    mx = sum(xs) / len(xs)
    centered = [x - mx for x in xs]
    if max(xs) == min(xs):
        raise CorpusError("stdlib measurements have no rank variation; increase task coverage")
    intercept, slope = sum(ys) / len(ys), 0.0
    step = 0.25 / (1 + max(x * x for x in centered) + ridge)
    for _ in range(1000):
        residuals = [
            min(0.0, intercept + slope * x - y) if r["censored"] else intercept + slope * x - y
            for x, y, r in zip(centered, ys, rows)
        ]
        intercept -= step * sum(residuals) / len(rows)
        slope = max(0.0, slope - step * (sum(d * x for d, x in zip(residuals, centered)) + ridge * slope) / len(rows))
    return Model(intercept - slope * mx, slope, ridge, target)


def error(model, labels):
    rows = [r for r in labels if r["status"] == "solved"]
    if not rows:
        return None
    return sum(
        (math.log(model.predict(r["rank_bound"])) - math.log(max(1e-9, r[model.target]))) ** 2 for r in rows
    ) / len(rows)


def train(config: Config):
    start = monotonic()
    deadline = start + config.budget
    tasks, corpus = collect(config.seed, deadline)
    training = [t for t in tasks if t.split == "train"]
    validation = [t for t in tasks if t.split == "validation"]
    held_out = [t for t in tasks if t.split == "held_out"]
    patterns = mine(training, config.min_support, config.max_patterns)
    if not patterns:
        raise CorpusError(
            "no repeated compressing stdlib training patterns; use --min-support 1 for an explicit small-corpus experiment"
        )
    labels, archive = [], {t.id: {t.reference} for t in training}

    def run(group, macros, phase):
        rows = []
        for task in group:
            if monotonic() >= deadline:
                rows.append(
                    {
                        "task": task.id,
                        "split": task.split,
                        "phase": phase,
                        "status": "global_budget",
                        "censored": True,
                        "candidates": 0,
                        "elapsed": 0,
                        "validation_failures": 0,
                    }
                )
                continue
            record, solution = reconstruct(task, macros, config, deadline)
            record["phase"] = phase
            rows.append(record)
            if task.split == "train" and solution is not None:
                archive[task.id].add(solution)
        return rows

    labels.extend(run(training, (), "initial"))
    validation_base = run(validation, (), "validation_baseline")
    # Validation selects a regularization coefficient; no held-out observations.
    models = [fit(labels, ridge=r) for r in (0.0, 1.0, 10.0)]
    model = min(
        models,
        key=lambda m: (error(m, validation_base) if error(m, validation_base) is not None else float("inf"), m.ridge),
    )
    runtime_model = fit(labels, target="elapsed", ridge=model.ridge)
    selected: list[dict] = []
    best: list[dict] = []
    history: list[dict] = []

    def validation_score(rows):
        return (
            -sum(r["status"] == "solved" for r in rows),
            sum(r["candidates"] if r["status"] == "solved" else config.max_candidates for r in rows),
        )

    best_score = validation_score(validation_base)

    def estimate(records, fitted):
        macros = tuple(production(r) for r in records)
        total = 0.0
        for task in training:
            grammar = Grammar(base_productions(task.inputs) + macros)
            ranks = [grammar.estimate(e) for e in archive[task.id]]
            ranks = [r for r in ranks if r is not None]
            if not ranks:
                return float("inf")
            total += fitted.predict(min(ranks))
        return total

    for iteration in range(config.iterations):
        if monotonic() >= deadline or len(selected) >= config.max_macros:
            break
        before = estimate(selected, model)
        proposals = [(estimate(selected + [p], model), p) for p in patterns if p not in selected]
        if not proposals:
            break
        score, proposal = min(proposals, key=lambda pair: (pair[0], pair[1]["id"]))
        step = {
            "iteration": iteration,
            "before_estimate": before,
            "proposals": [{"macro": p["id"], "estimate": s} for s, p in proposals],
            "archive_before": {k: len(v) for k, v in archive.items()},
        }
        history.append(step)
        if score >= before:
            step["stop"] = "no predicted improvement"
            break
        selected.append(proposal)
        macros = tuple(production(r) for r in selected)
        refresh = run(training, macros, f"refresh_{iteration}")
        labels.extend(refresh)
        validation_rows = run(validation, macros, f"validation_{iteration}")
        step.update(
            selected=proposal["id"],
            refresh=refresh,
            validation=validation_rows,
            archive_after={k: len(v) for k, v in archive.items()},
        )
        # Tie-break toward an equally validated additions-only profile.
        if (
            all(r["status"] != "global_budget" for r in validation_rows)
            and validation_score(validation_rows) <= best_score
        ):
            best, best_score = list(selected), validation_score(validation_rows)
        model = fit(labels, ridge=model.ridge)
        runtime_model = fit(labels, target="elapsed", ridge=model.ridge)
    # Freeze selection/model before inspecting final held-out references/results.
    frozen = tuple(production(r) for r in best)
    held_baseline = run(held_out, (), "held_out_baseline")
    held_optimized = run(held_out, frozen, "held_out_optimized")
    if not best:
        # This is a real trained baseline profile, not pretend macro acceleration.
        selection_reason = "validation retained the original grammar; no additions earned selection"
    else:
        selection_reason = "rank-cost search, selected by stdlib validation coverage/candidate counts"
    return {
        "schema": 1,
        "grammar_version": GRAMMAR_VERSION,
        "feature_version": FEATURE_VERSION,
        "config": asdict(config),
        "corpus": corpus,
        "base_grammar": "fixed total Int/Bool primitives, constants 0/1/false/true, inference locals",
        "macros": patterns,
        "selected": [p["id"] for p in best],
        "selection_reason": selection_reason,
        "cost_model": asdict(model),
        "runtime_model": asdict(runtime_model),
        "model_loss": "log-cost ridge regression; one-sided squared loss for measured censored lower bounds",
        "labels": labels,
        "validation_baseline": validation_base,
        "search": history,
        "known_solutions": {k: [e.data() for e in sorted(v, key=repr)] for k, v in archive.items()},
        "held_out": {
            "baseline": held_baseline,
            "optimized": held_optimized,
            "candidate_model_log_mse": error(model, held_optimized),
            "runtime_model_log_mse": error(runtime_model, held_optimized),
        },
        "offline_seconds": monotonic() - start,
        "stop_reason": "global_budget" if monotonic() >= deadline else "bounded_search_complete",
        "limitations": "Small stdlib pilot. Whole-expression enumerator; derivation-count upper bounds. No deletions, GP/cvc5 integration, ADTs, polymorphism, refined training signatures, recursion, opaque helpers or user-task learning.",
    }
