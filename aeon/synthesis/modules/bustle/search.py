"""BUSTLE Algorithm 1: weighted bottom-up enumeration of concrete value vectors."""

from __future__ import annotations

import itertools
import time
from collections.abc import Callable, Iterator, Sequence
from dataclasses import dataclass, field

from aeon.core.terms import If, Term
from aeon.synthesis.modules.bustle.values import identity
from aeon.synthesis.modules.bottom_up import application
from aeon.synthesis.modules.bustle.signatures import (
    Scalar,
    probability_penalty,
    task_signature,
    valid_scalar,
    value_signature,
)


@dataclass(frozen=True)
class Operation:
    head: Term
    arg_keys: tuple[str, ...]
    ret_key: str
    execute: Callable[[tuple[Scalar, ...]], Scalar]
    conditional: bool = False


@dataclass(frozen=True)
class Value:
    term: Term
    key: str
    outputs: tuple[Scalar, ...]
    weight: int = 1
    children: tuple[Value, ...] = ()


@dataclass
class SearchStats:
    generated: int = 0
    unique: int = 0
    duplicates: int = 0
    invalid: int = 0
    model_calls: int = 0
    reweighted: int = 0
    final_weight: int = 1
    stopped: str = "exhausted"
    values: list[Value] = field(default_factory=list)


def weight_partitions(total: int, arity: int) -> Iterator[tuple[int, ...]]:
    """All ordered positive partitions: an operation contributes one node."""
    if arity == 1:
        if total >= 1:
            yield (total,)
        return
    for first in range(1, total - arity + 2):
        for rest in weight_partitions(total - first, arity - 1):
            yield (first, *rest)


def enumerate_values(
    atoms: Sequence[Value],
    operations: Sequence[Operation],
    inputs: Sequence[Sequence[Scalar]],
    expected: tuple[Scalar, ...],
    *,
    accept: Callable[[Value], bool],
    predict: Callable[[list[tuple[int, ...]]], Sequence[float]] | None,
    deadline: float,
    max_weight: int = 40,
    max_values: int = 20_000,
    batch_size: int = 128,
    stats: SearchStats | None = None,
    valid: Callable[[object, str], bool] = valid_scalar,
) -> Value | None:
    """Store each semantic value once, then expand by *adjusted* child weights.

    Model penalties are nonnegative, so batched reweighting never schedules a
    child before its generating round. Leaves stay at weight 1 (paper line 6).
    Acceptance is checked before merging: alternate representatives with the
    same examples can still discharge different Aeon refinements.
    """
    if max_weight < 1 or max_values < 1 or batch_size < 1:
        raise ValueError("BUSTLE search bounds must be positive")
    stats = stats if stats is not None else SearchStats()
    bank: dict[int, dict[str, list[Value]]] = {}
    seen: set[tuple] = set()
    pending: list[Value] = []
    signature = task_signature(inputs, expected) if predict is not None else ()

    def store(value: Value) -> None:
        bank.setdefault(value.weight, {}).setdefault(value.key, []).append(value)
        stats.values.append(value)

    def flush() -> None:
        if not pending:
            return
        if predict is None:
            penalties = [0] * len(pending)
        else:
            features = [signature + value_signature(value.outputs, expected) for value in pending]
            probabilities = predict(features)
            if len(probabilities) != len(pending):
                raise ValueError("BUSTLE model returned the wrong batch size")
            penalties = [probability_penalty(float(p)) for p in probabilities]
            stats.model_calls += 1
        for value, penalty in zip(pending, penalties):
            if penalty:
                stats.reweighted += 1
            store(Value(value.term, value.key, value.outputs, value.weight + penalty, value.children))
        pending.clear()

    def consider(value: Value, leaf: bool = False) -> bool:
        stats.generated += 1
        if len(value.outputs) != len(expected) or not all(valid(v, value.key) for v in value.outputs):
            stats.invalid += 1
            return False
        if accept(value):
            stats.stopped = "solution"
            return True
        observation = (value.key, tuple(identity(v) for v in value.outputs))
        if observation in seen:
            stats.duplicates += 1
            return False
        seen.add(observation)
        stats.unique += 1
        if leaf:
            store(value)
        else:
            pending.append(value)
            if len(pending) >= batch_size:
                flush()
        return False

    for atom in atoms:
        if time.monotonic() >= deadline:
            stats.stopped = "budget"
            return None
        if consider(atom, leaf=True):
            return atom
        if stats.unique >= max_values:
            stats.stopped = "value limit"
            return None
    for weight in range(2, max_weight + 1):
        stats.final_weight = weight
        for op in operations:
            for partition in weight_partitions(weight - 1, len(op.arg_keys)):
                pools = [bank.get(w, {}).get(key, []) for w, key in zip(partition, op.arg_keys)]
                if any(not pool for pool in pools):
                    continue
                for children in itertools.product(*pools):
                    if time.monotonic() >= deadline:
                        stats.stopped = "budget"
                        return None
                    try:
                        outputs = tuple(
                            op.execute(tuple(child.outputs[i] for child in children)) for i in range(len(expected))
                        )
                    except Exception:
                        # A DSL primitive may fail on these inputs. Keep model
                        # and search exceptions outside this narrow execution guard.
                        stats.generated += 1
                        stats.invalid += 1
                        continue
                    terms = tuple(child.term for child in children)
                    term = If(terms[0], terms[1], terms[2]) if op.conditional else application(op.head, terms)
                    value = Value(term, op.ret_key, outputs, weight, children)
                    if consider(value):
                        return value
                    if stats.unique >= max_values:
                        flush()
                        stats.stopped = "value limit"
                        return None
        flush()
    return None
