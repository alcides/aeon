"""Pandas-backed DataFrame bindings for ``DataFrame.ae``.

Orchestration (I/O, select, join, groupby) stays in pandas. Dense numeric
columns cross the Array bridge via ``col_as_array`` / ``set_col`` so ``@llvm``
/ ``@gpu`` kernels can run on contiguous buffers.
"""

from __future__ import annotations

from typing import Any, Callable, TypeAlias

import numpy as np
import pandas as pd

from aeon.bindings.binding_utils import curried


DataFrame: TypeAlias = pd.DataFrame


def read_csv(path: str) -> DataFrame:
    return pd.read_csv(path)


@curried
def to_csv(df: DataFrame, path: str) -> None:
    df.to_csv(path, index=False)


def nrows(df: DataFrame) -> int:
    return int(len(df))


def ncols(df: DataFrame) -> int:
    return int(df.shape[1])


def columns(df: DataFrame) -> list[str]:
    return [str(c) for c in df.columns]


@curried
def has_col(df: DataFrame, name: str) -> bool:
    return name in df.columns


@curried
def head(df: DataFrame, n: int) -> DataFrame:
    return df.head(n).copy()


@curried
def select(df: DataFrame, cols: list[str]) -> DataFrame:
    return df.loc[:, list(cols)].copy()


@curried
def drop(df: DataFrame, cols: list[str]) -> DataFrame:
    return df.drop(columns=list(cols)).copy()


@curried
def rename(df: DataFrame, old: str, new: str) -> DataFrame:
    return df.rename(columns={old: new}).copy()


@curried
def filter_rows(df: DataFrame, column: str, pred: Callable[[Any], bool]) -> DataFrame:
    mask = df[column].map(pred)
    return df.loc[mask].copy()


@curried
def dropna(df: DataFrame) -> DataFrame:
    return df.dropna().copy()


@curried
def fillna(df: DataFrame, value: float) -> DataFrame:
    return df.fillna(value).copy()


@curried
def sort_values(df: DataFrame, column: str, ascending: bool) -> DataFrame:
    return df.sort_values(by=column, ascending=ascending).copy()


@curried
def concat(left: DataFrame, right: DataFrame) -> DataFrame:
    return pd.concat([left, right], ignore_index=True)


@curried
def join(left: DataFrame, right: DataFrame, on: str, how: str) -> DataFrame:
    return left.merge(right, on=on, how=how)


@curried
def groupby_agg(df: DataFrame, by: str, column: str, how: str) -> DataFrame:
    agg = {"sum": "sum", "mean": "mean", "count": "count", "min": "min", "max": "max"}.get(how, how)
    out = df.groupby(by, as_index=False)[column].agg(agg)
    out.columns = [by, column]
    return out


@curried
def col_as_array(df: DataFrame, name: str) -> list[float]:
    return list(np.asarray(df[name], dtype=float).reshape(-1))


@curried
def set_col(df: DataFrame, name: str, values: list[Any]) -> DataFrame:
    out = df.copy()
    out[name] = list(values)
    return out


@curried
def assign_const(df: DataFrame, name: str, value: float) -> DataFrame:
    out = df.copy()
    out[name] = value
    return out


def copy_df(df: DataFrame) -> tuple[DataFrame, DataFrame]:
    return df, df.copy()


@curried
def with_col(df: DataFrame, name: str) -> tuple[DataFrame, list[float]]:
    return df, list(np.asarray(df[name], dtype=float).reshape(-1))


@curried
def map_col(df: DataFrame, name: str, f: Callable[[list[Any]], list[Any]]) -> DataFrame:
    values = list(np.asarray(df[name], dtype=float).reshape(-1))
    out = df.copy()
    out[name] = list(f(values))
    return out
