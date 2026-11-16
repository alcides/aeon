"""Runtime witnesses for value-domain refinements at native boundaries.

These predicates inspect values without changing them. They do not promise that
external resources will remain available after a check.
"""

from __future__ import annotations

import json
from pathlib import PurePath
from typing import Any, Callable


def json_source(source: str) -> bool:
    try:
        json.loads(source)
        return True
    except (ValueError, RecursionError):
        return False


def parseable(source: str, convert: Callable[[str], Any]) -> bool:
    try:
        convert(source)
        return True
    except (ValueError, OverflowError):
        return False


def string_to_int(source: str) -> int:
    if not source.isdigit():
        return -1
    try:
        return int(source)
    except ValueError:
        return -1


def contest_integers(source: str) -> tuple:
    result: tuple = ("Seq_nil",)
    for token in reversed(source.split()):
        result = ("Seq_cons", int(token), result)
    return result


def suffix_allowed(path: PurePath, suffix: str) -> bool:
    try:
        path.with_suffix(suffix)
        return True
    except ValueError:
        return False


def plot_marker(marker: str) -> bool:
    from matplotlib.markers import MarkerStyle

    try:
        MarkerStyle(marker)
        return True
    except (ValueError, TypeError):
        return False


def numeric_column(frame: Any, name: str) -> bool:
    """A unique column whose cells can be passed to Float callbacks."""
    from pandas.api.types import is_numeric_dtype, is_complex_dtype
    from numbers import Real

    if name not in frame.columns or list(frame.columns).count(name) != 1:
        return False
    column = frame[name]
    return bool(is_numeric_dtype(column) and not is_complex_dtype(column) and all(isinstance(v, Real) for v in column))


def argument_name(parser: Any, name: str) -> bool:
    import re

    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", name):
        return False
    return (
        all(action.dest not in {name, name.replace("-", "_")} for action in parser._actions)
        and "--" + name not in parser._option_string_actions
    )


def learning_split(ds: Any, fraction: float) -> bool:
    import math

    if not 0.0 < fraction < 1.0:
        return False
    rows = len(ds[0])
    test = math.ceil(rows * (1.0 - fraction))
    return 0 < test < rows


def stratified_split(ds: Any, fraction: float) -> bool:
    import math
    from collections import Counter

    if not 0.0 < fraction < 1.0:
        return False
    rows = len(ds[0])
    counts = Counter(ds[1])
    train = math.floor(rows * fraction)
    return bool(counts) and min(counts.values()) >= 2 and train >= len(counts) and rows - train >= len(counts)


def column_family(frame: Any, name: str) -> str | None:
    from pandas.api.types import is_string_dtype

    if name not in frame.columns or list(frame.columns).count(name) != 1:
        return None
    if numeric_column(frame, name):
        return "number"
    column = frame[name]
    if is_string_dtype(column) and all(isinstance(value, str) for value in column.dropna()):
        return "string"
    return None


def joinable_column(left: Any, right: Any, name: str) -> bool:
    family = column_family(left, name)
    return family is not None and family == column_family(right, name)
