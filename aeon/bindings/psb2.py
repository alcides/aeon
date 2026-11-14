"""Stable PSB2 fixtures which hand each fitness evaluation its own data."""

from copy import deepcopy
import math
import random
from typing import Any, Callable

from aeon.bindings.lists import from_iterable, to_list


def training_data(name: str, n_train: int, n_test: int) -> Callable[[Any], Any]:
    """Sample once, lazily, and copy the same cases for every candidate.

    Candidates may consume or mutate array inputs. Neither that mutation nor
    another call to PSB2's random sampler may change the next evaluation's
    training cases. The private template is never returned to Aeon.
    """
    template = None

    def fresh(_unit: Any) -> Any:
        nonlocal template
        if template is None:
            from psb2 import fetch_examples

            # A fixture copied to a fitness worker before first use must draw
            # the same cases there too. PSB2 seeds the process-wide RNG, so
            # restore it rather than perturbing synthesis search randomness.
            state = random.getstate()
            try:
                template = fetch_examples("path/to/PSB2/datasets/", name, n_train, n_test, format="lists", seed=0)[0]
            finally:
                random.setstate(state)
        return deepcopy(template)

    return fresh


# Dataset rows are (input columns, output columns). A vector is one column,
# while coin sums, find pair, cut vector and mastermind have multiple outputs.
_INPUTS = {
    "basement": ("ints",),
    "bouncing-balls": ("float", "float", "int"),
    "bowling": ("str",),
    "camel-case": ("str",),
    "coin-sums": ("int",),
    "cut-vector": ("ints",),
    "dice-game": ("int", "int"),
    "find-pair": ("ints", "int"),
    "fizz-buzz": ("int",),
    "fuel-cost": ("ints",),
    "gcd": ("int", "int"),
    "indices-of-substring": ("str", "str"),
    "leaders": ("ints",),
    "luhn": ("ints",),
    "mastermind": ("str", "str"),
    "middle-character": ("str",),
    "paired-digits": ("str",),
    "shopping-list": ("floats", "floats"),
    "snow-day": ("int", "float", "float", "float"),
    "solve-boolean": ("str",),
    "spin-words": ("str",),
    "square-digits": ("int",),
    "substitution-cipher": ("str", "str", "str"),
    "twitter": ("str",),
    "vector-distance": ("floats", "floats"),
}
_MULTIPLE_OUTPUTS = {"coin-sums", "cut-vector", "find-pair", "mastermind"}
_LIST_OUTPUTS = _MULTIPLE_OUTPUTS | {"indices-of-substring", "leaders"}


def _input(kind: str, value: Any) -> Any:
    if kind in {"ints", "floats"}:
        return from_iterable(_input(kind[:-1], x) for x in value)
    if kind == "float" and type(value) in {int, float} and math.isfinite(value):
        return float(value)
    if (kind == "int" and type(value) is int) or (kind == "str" and isinstance(value, str)):
        return value
    raise ValueError(f"invalid PSB2 {kind} input: {value!r}")


def _output(problem: str, value: Any) -> Any:
    if problem == "cut-vector":
        return [to_list(xs) for xs in to_list(value)]
    if problem in _LIST_OUTPUTS:
        return to_list(value)
    return value


def _valid_domain(problem: str, args: list) -> bool:
    """Check the preconditions promised by the Aeon fitness callback types."""

    def vector(xs, lo, hi, minimum=0, maximum=20):
        return minimum <= len(xs) <= maximum and all(lo <= x <= hi for x in xs)

    a = args[0]
    if problem == "basement":
        return vector(a, -100, 100, 1)
    if problem == "bouncing-balls":
        return 1.0 <= a <= 100.0 and 1.0 <= args[1] < a and 1 <= args[2] <= 20
    if problem == "bowling":
        return 12 <= len(a) <= 21
    if problem == "coin-sums":
        return 1 <= a <= 10000
    if problem == "cut-vector":
        return vector(a, 0, 10000, 1)
    if problem == "dice-game":
        return all(1 <= x <= 1000 for x in args)
    if problem == "find-pair":
        return vector(a, -10000, 10000, 2) and -20000 <= args[1] <= 20000
    if problem == "fizz-buzz":
        return 1 <= a <= 1000000
    if problem == "fuel-cost":
        return vector(a, 6, 10000, 1)
    if problem == "gcd":
        return all(1 <= x <= 1000000 for x in args)
    if problem == "indices-of-substring":
        return all(1 <= len(x) <= 20 for x in args)
    if problem == "leaders":
        return vector(a, 0, 1000)
    if problem == "luhn":
        return vector(a, 0, 9, 16, 16)
    if problem == "mastermind":
        return all(len(x) == 4 for x in args)
    if problem == "middle-character":
        return 1 <= len(a) <= 100
    if problem == "paired-digits":
        return 2 <= len(a) <= 20
    if problem == "shopping-list":
        return vector(a, 0.0, 50.0, 1) and vector(args[1], 0.0, 100.0, len(a), len(a))
    if problem == "snow-day":
        return 0 <= a <= 20 and 0.0 <= args[1] <= 20.0 and args[2] >= 0.0 and 0.0 <= args[3] <= 1.0
    if problem == "solve-boolean":
        return 1 <= len(a) <= 39 and len(a) % 2 == 1
    if problem == "square-digits":
        return 0 <= a <= 1000000
    if problem == "substitution-cipher":
        return len(a) <= 26 and len(args[1]) == len(a) and len(args[2]) <= 26
    if problem == "twitter":
        return len(a) <= 200
    if problem == "vector-distance":
        return vector(a, -100.0, 100.0, 1) and vector(args[1], -100.0, 100.0, len(a), len(a))
    return True  # camel-case and spin-words accept unrestricted strings.


def _error(actual: Any, expected: Any) -> float:
    if isinstance(expected, list):
        if not isinstance(actual, list):
            raise ValueError("expected a PSB2 sequence result")
        return 1000.0 * abs(len(actual) - len(expected)) + sum(_error(a, b) for a, b in zip(actual, expected))
    if isinstance(expected, str):
        if not isinstance(actual, str):
            raise ValueError("expected a PSB2 string result")
        from textdistance import levenshtein

        return float(levenshtein(actual, expected))
    if isinstance(expected, bool):
        if not isinstance(actual, bool):
            raise ValueError("expected a PSB2 Boolean result")
        return float(actual != expected)
    if type(actual) not in {int, float} or not math.isfinite(actual):
        raise ValueError("expected a finite PSB2 numeric result")
    return float(abs(actual - expected))


def errors(problem: str, data: list, candidate: Callable) -> list[float]:
    """Apply a curried Aeon candidate to correctly typed dataset columns.

    Score each row independently, including every element of nested outputs.
    Conversion preserves floats and immutable List structure; it never flattens
    examples or pretends that heterogeneous columns are Array Int values.
    """
    kinds = _INPUTS[problem]
    result = []
    for inputs, outputs in data:
        if len(inputs) != len(kinds):
            raise ValueError(f"unexpected PSB2 input arity for {problem}")
        converted = [_input(kind, value) for kind, value in zip(kinds, inputs)]
        if not _valid_domain(problem, inputs):
            raise ValueError(f"PSB2 input violates {problem} refinements")
        actual: Any = candidate
        for value in converted:
            actual = actual(value)
        if problem not in _MULTIPLE_OUTPUTS and len(outputs) != 1:
            raise ValueError(f"unexpected PSB2 output arity for {problem}")
        expected = outputs if problem in _MULTIPLE_OUTPUTS else outputs[0]
        result.append(_error(_output(problem, actual), expected))
    return result
