"""Representative sampling against a bounded history, plus uniform/full baselines."""

from itertools import combinations
from math import comb
from time import monotonic

from aeon.synthesis.modules.noisy.model import SamplingRound, risk


def discrepancy(history, sample, count):
    return max((abs(risk(losses, range(count)) - risk(losses, sample)) for losses in history), default=0.0)


def select_sample(history, count, size, rng, config, deadline):
    size = min(count, size)
    if size == count or config.sampler == "full":
        sample = tuple(range(count))
        return SamplingRound(sample, discrepancy(history, sample, count), "full", len(history))
    initial = tuple(sorted(rng.sample(range(count), size)))
    if config.sampler == "uniform" or not history:
        return SamplingRound(initial, discrepancy(history, initial, count), "uniform", len(history))
    best = initial
    score = discrepancy(history, best, count)
    if comb(count, size) <= config.exact_subsets:
        method = "exact"
        for candidate in combinations(range(count), size):
            if monotonic() >= deadline:
                method = "exact interrupted"
                break
            delta = discrepancy(history, candidate, count)
            if (delta, candidate) < (score, best):
                best, score = candidate, delta
    else:
        method = "greedy exchanges (heuristic)"
        for _ in range(config.exchange_trials):
            if monotonic() >= deadline:
                break
            inside = rng.choice(best)
            outside = rng.randrange(count)
            if outside in best:
                continue
            candidate = tuple(sorted((set(best) - {inside}) | {outside}))
            delta = discrepancy(history, candidate, count)
            if (delta, candidate) < (score, best):
                best, score = candidate, delta
    return SamplingRound(best, score, method, len(history))
