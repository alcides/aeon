"""Approximate regularized generation and history-guided sampling coordinator."""

from collections import OrderedDict
from dataclasses import dataclass, field
import random
from time import monotonic

from aeon.synthesis.api import InvalidIndividualException, SynthesisNotSuccessful
from aeon.synthesis.modules.noisy.model import Report, Residual, risk, same_value, scalar
from aeon.synthesis.modules.noisy.sampling import select_sample
from aeon.synthesis.modules.noisy.structure import identity, complexity
from aeon.synthesis.modules.noisy.worker import Worker, WorkerError, WorkerTimeout


@dataclass
class Record:
    term: object
    key: tuple
    size: int
    actual: dict = field(default_factory=dict)
    losses: dict = field(default_factory=dict)
    complete: bool = False


class EnumerationGenerator:
    """A bounded, persistent enumeration adapter; samples rank its archive."""

    def __init__(self, next_candidate, config):
        self.next_candidate = next_candidate
        self.config = config
        self.archive = OrderedDict()
        self.exhausted = False
        self.generated = 0
        self.rejected = 0

    def generate(self, sample, oracle, remaining, deadline):
        round_deadline = min(deadline, monotonic() + remaining)
        for _ in range(self.config.candidates_per_round):
            if self.exhausted or monotonic() >= round_deadline:
                break
            term = self.next_candidate()
            if term is None:
                self.exhausted = True
                break
            self.generated += 1
            try:
                key = identity(term)
            except (InvalidIndividualException, RecursionError):
                self.rejected += 1
                continue
            self.archive[key] = term
            if len(self.archive) > self.config.archive_size:
                self.archive.popitem(last=False)
        ranked = []
        for term in self.archive.values():
            if monotonic() >= deadline:
                raise WorkerTimeout()
            record = oracle(term, sample)
            if record is not None:
                error = risk(record.losses, sample)
                ranked.append(
                    ((error + self.config.regularization * record.size, error, record.size, record.key), record)
                )
        ranked.sort(key=lambda item: item[0])
        # Full-score two sample finalists, so history is not just the latest
        # winner. The coordinator also retains every other fully scored record.
        return [record for _, record in ranked[:2]]


def run_search(dataset, config, seed, stream, validate, probe, inputs, definitions, ui, budget, domain_check=None):
    started = monotonic()
    deadline = started + max(0, budget)
    rng = random.Random(seed)
    count = len(dataset.rows)
    cache = OrderedDict()
    history = OrderedDict()
    incumbent = None
    incumbent_rank = None
    rounds = []
    validated = invalid = fully_scored = row_evaluations = 0
    stop_reason = "round_limit"

    def observe(argument):
        term, indices = argument
        return tuple(probe(term, dataset.rows[index].inputs) for index in indices)

    worker = Worker(
        {
            "next": lambda _: next(stream, None),
            "validate": validate,
            "observe": observe,
            "domain": lambda _: domain_check() if domain_check else True,
        }
    )

    def call(operation, argument):
        value = worker.call(operation, argument, min(config.call_timeout, deadline - monotonic()))
        if monotonic() >= deadline:
            raise WorkerTimeout()
        return value

    generator = EnumerationGenerator(lambda: call("next", None), config)

    def complete(record):
        nonlocal incumbent, incumbent_rank, fully_scored
        if monotonic() >= deadline:
            raise WorkerTimeout()
        if record.complete or len(record.losses) != count:
            return
        record.complete = True
        fully_scored += 1
        error = risk(record.losses, range(count))
        rank = (error + config.regularization * record.size, error, record.size, record.key)
        if incumbent_rank is None or rank < incumbent_rank:
            incumbent, incumbent_rank = record, rank
            ui.register(record.term, [rank[0]], monotonic() - started, True)
        history[record.key] = tuple(record.losses[i] for i in range(count))
        while len(history) > config.history_size:
            oldest = next(key for key in history if incumbent is None or key != incumbent.key)
            del history[oldest]

    def oracle(term, indices):
        nonlocal validated, invalid, row_evaluations
        key = identity(term)
        if key not in cache:
            try:
                size = complexity(term, inputs, definitions)
                validated += 1
                if not call("validate", term):
                    raise InvalidIndividualException()
                cache[key] = Record(term, key, size)
            except (WorkerError, InvalidIndividualException, RecursionError):
                invalid += 1
                cache[key] = None
            except WorkerTimeout:
                invalid += 1
                raise
            if len(cache) > config.cache_size:
                cache.popitem(last=False)
        record = cache[key]
        cache.move_to_end(key)
        if record is None:
            return None
        missing = tuple(i for i in indices if i not in record.losses)
        if missing:
            try:
                actual = call("observe", (term, missing))
                if len(actual) != len(missing) or any(not scalar(v) for v in actual):
                    raise InvalidIndividualException()
                # An evaluator returning the wrong scalar type is invalid, not
                # a mislabeled row. Bool and Int never compare interchangeably.
                if any(type(value) is not type(dataset.rows[i].expected) for i, value in zip(missing, actual)):
                    raise InvalidIndividualException()
                for i, value in zip(missing, actual):
                    record.actual[i] = value
                    record.losses[i] = int(not same_value(value, dataset.rows[i].expected))
                row_evaluations += len(missing)
            except (WorkerError, InvalidIndividualException):
                invalid += 1
                cache[key] = None
                return None
            except WorkerTimeout:
                invalid += 1
                cache[key] = None
                raise
        complete(record)
        return record

    try:
        if not call("domain", None):
            from aeon.synthesis.api import UnsupportedSynthesisGoal

            raise UnsupportedSynthesisGoal("Noisy observations violate an input type/precondition")
        size = min(config.initial_sample, count)
        for iteration in range(config.rounds):
            if monotonic() >= deadline:
                raise WorkerTimeout()
            sample = select_sample(tuple(history.values()), count, size, rng, config, deadline)
            rounds.append(sample)
            remaining = (deadline - monotonic()) / max(1, config.rounds - iteration)
            finalists = generator.generate(sample.sample, oracle, remaining, deadline)
            for record in finalists:
                oracle(record.term, tuple(range(count)))
            if len(sample.sample) == count and generator.exhausted:
                stop_reason = "full_sample"
                break
            if generator.exhausted and not generator.archive:
                stop_reason = "generator_exhausted"
                break
            size = min(count, max(size + 1, size * 2))
    except WorkerTimeout:
        stop_reason = "budget" if monotonic() >= deadline else "worker_timeout"
    except WorkerError:
        stop_reason = "worker_error"
    finally:
        worker.close()
    if incumbent is None:
        raise SynthesisNotSuccessful(f"noisy: no validated, fully scored candidate ({stop_reason})")
    assert incumbent_rank is not None
    report = Report(
        empirical_error=incumbent_rank[1],
        regularization=config.regularization,
        regularization_term=config.regularization * incumbent.size,
        complexity=incumbent.size,
        objective=incumbent_rank[0],
        row_count=count,
        residuals=tuple(
            Residual(i, dataset.rows[i].expected, incumbent.actual[i]) for i in range(count) if incumbent.losses[i]
        ),
        rounds=tuple(rounds),
        seed=seed,
        stop_reason=stop_reason,
        candidates_generated=generator.generated,
        candidates_validated=validated,
        candidates_fully_scored=fully_scored,
        invalid_candidates=invalid + generator.rejected,
        row_evaluations=row_evaluations,
        elapsed_seconds=monotonic() - started,
    )
    return incumbent.term, report
