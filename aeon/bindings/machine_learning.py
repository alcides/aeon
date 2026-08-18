from __future__ import annotations

import csv
from dataclasses import dataclass, field
from numbers import Integral, Real
from typing import Any, Callable

import numpy as np
import pandas as pd
from sklearn.compose import ColumnTransformer
from sklearn.impute import SimpleImputer
from sklearn.model_selection import train_test_split
from sklearn.pipeline import Pipeline
from sklearn.preprocessing import OneHotEncoder
from sklearn.tree import DecisionTreeClassifier

from aeon.bindings.binding_utils import curried


class MLRestrictionError(ValueError):
    """Raised when a runtime ML restriction cannot be satisfied."""


class MLResourceConsumedError(MLRestrictionError):
    """Raised when native code tries to reuse a consumed linear resource."""


@dataclass(slots=True)
class DataFrame:
    """Owned wrapper around a pandas DataFrame."""

    value: pd.DataFrame
    _consumed: bool = field(default=False, init=False, repr=False)


@dataclass(slots=True)
class Dataset:
    """Owned, labelled dataset before the train/test split."""

    features: pd.DataFrame
    target: pd.Series
    _consumed: bool = field(default=False, init=False, repr=False)


@dataclass(slots=True)
class TrainingDataset:
    """Owned training half produced by a split."""

    features: pd.DataFrame
    target: pd.Series
    split_token: object = field(repr=False)
    _consumed: bool = field(default=False, init=False, repr=False)


@dataclass(slots=True)
class TestingDataset:
    """Owned testing half produced by a split."""

    features: pd.DataFrame
    target: pd.Series
    split_token: object = field(repr=False)
    _consumed: bool = field(default=False, init=False, repr=False)


@dataclass(slots=True)
class DatasetSplit:
    """Owned pair that can be eliminated once through ``consume_split``."""

    training: TrainingDataset
    testing: TestingDataset
    _consumed: bool = field(default=False, init=False, repr=False)


LinearResource = DataFrame | Dataset | TrainingDataset | TestingDataset | DatasetSplit


def _require_available(resource: LinearResource, expected_type: type, operation: str) -> None:
    if not isinstance(resource, expected_type):
        raise TypeError(f"{operation} esperava {expected_type.__name__}, recebeu {type(resource).__name__}")
    if resource._consumed:
        raise MLResourceConsumedError(f"{expected_type.__name__} já foi consumido por uma operação anterior")


def _mark_consumed(resource: LinearResource) -> None:
    resource._consumed = True


def _validate_frame(frame: pd.DataFrame) -> None:
    rows, columns = frame.shape
    if rows < 4:
        raise MLRestrictionError(f"read_csv exige pelo menos 4 linhas; o CSV tem {rows}")
    if columns < 2:
        raise MLRestrictionError(f"read_csv exige target e pelo menos uma feature; o CSV tem {columns} coluna(s)")
    if frame.columns.has_duplicates:
        duplicates = frame.columns[frame.columns.duplicated()].tolist()
        raise MLRestrictionError(f"os nomes das colunas têm de ser únicos; duplicados: {duplicates!r}")


def read_csv(path: str) -> DataFrame:
    """Read and validate a CSV, returning a fresh owned DataFrame."""
    # pandas disambiguates duplicate headers automatically (``x``, ``x.1``),
    # which would hide an ambiguous source schema.  Inspect the original header
    # before parsing so the uniqueness restriction remains observable.
    with open(path, newline="", encoding="utf-8-sig") as source:
        header = next(csv.reader(source), None)
    if header is not None and len(header) != len(set(header)):
        duplicates = sorted({name for name in header if header.count(name) > 1})
        raise MLRestrictionError(f"os nomes das colunas têm de ser únicos; duplicados: {duplicates!r}")

    frame = pd.read_csv(path)
    _validate_frame(frame)
    return DataFrame(frame)


@curried
def target(df: DataFrame, column: int) -> Dataset:
    """Consume ``df`` and designate a valid zero-based target column."""
    _require_available(df, DataFrame, "target")
    if isinstance(column, bool) or not isinstance(column, (Integral, np.integer)):
        raise TypeError(f"o índice do target tem de ser Int, recebeu {type(column).__name__}")

    index = int(column)
    column_count = len(df.value.columns)
    if index < 0 or index >= column_count:
        raise MLRestrictionError(f"índice de target {index} fora do intervalo válido [0, {column_count - 1}]")

    target_values = df.value.iloc[:, index].copy()
    if target_values.isna().any():
        missing_count = int(target_values.isna().sum())
        raise MLRestrictionError(f"a coluna target contém {missing_count} valor(es) em falta")

    class_counts = target_values.value_counts(dropna=False)
    if len(class_counts) < 2:
        raise MLRestrictionError("decision_tree_classifier exige pelo menos duas classes no target")
    rare_classes = class_counts[class_counts < 2]
    if not rare_classes.empty:
        details = {str(label): int(count) for label, count in rare_classes.items()}
        raise MLRestrictionError(
            f"o split estratificado exige pelo menos duas linhas por classe; classes insuficientes: {details}"
        )

    feature_positions = [position for position in range(column_count) if position != index]
    features = df.value.iloc[:, feature_positions].copy()
    dataset = Dataset(features=features, target=target_values)
    _mark_consumed(df)
    return dataset


@curried
def split(ds: Dataset, train_size: float) -> DatasetSplit:
    """Consume a dataset and create a deterministic, stratified split."""
    _require_available(ds, Dataset, "split")
    if isinstance(train_size, bool) or not isinstance(train_size, (Real, np.floating)):
        raise TypeError(f"train_size must be a float, and received {type(train_size).__name__}")

    fraction = float(train_size)
    if not np.isfinite(fraction) or not 0.0 < fraction < 1.0:
        raise MLRestrictionError(f"train_size must satisfy 0.0 < f < 1.0; received {fraction!r}")

    try:
        x_train, x_test, y_train, y_test = train_test_split(
            ds.features,
            ds.target,
            train_size=fraction,
            random_state=42,
            stratify=ds.target,
        )
    except ValueError as error:
        raise MLRestrictionError(f"could not create a valid stratified split: {error}") from error

    train_classes = set(y_train.unique().tolist())
    test_classes = set(y_test.unique().tolist())
    source_classes = set(ds.target.unique().tolist())
    if not x_train.index.is_unique or not x_test.index.is_unique:
        raise MLRestrictionError("the dataset index must uniquely identify each row")
    if not set(x_train.index).isdisjoint(set(x_test.index)):
        raise MLRestrictionError("the split produced overlapping rows in train and test sets")
    if train_classes != source_classes or test_classes != source_classes:
        raise MLRestrictionError("the chosen fraction does not preserve all classes in train and test sets")

    split_token = object()
    parts = DatasetSplit(
        training=TrainingDataset(x_train.copy(), y_train.copy(), split_token),
        testing=TestingDataset(x_test.copy(), y_test.copy(), split_token),
    )
    _mark_consumed(ds)
    return parts


@curried
def consume_split(parts: DatasetSplit, consumer: Callable[[TrainingDataset], Any]) -> Any:
    """Consume a split once and pass its two linear halves to ``consumer``."""
    _require_available(parts, DatasetSplit, "consume_split")
    if not callable(consumer):
        raise TypeError(f"consume_split esperava uma função, recebeu {type(consumer).__name__}")

    _mark_consumed(parts)
    result = consumer(parts.training)(parts.testing)
    if not parts.training._consumed or not parts.testing._consumed:
        missing: list[str] = []
        if not parts.training._consumed:
            missing.append("TrainingDataset")
        if not parts.testing._consumed:
            missing.append("TestingDataset")
        raise MLRestrictionError("o callback não consumiu exatamente os dois recursos: " + ", ".join(missing))
    return result


def _preprocessor(features: pd.DataFrame) -> ColumnTransformer:
    """Build preprocessing fitted exclusively by the training pipeline."""
    numeric_columns = list(features.select_dtypes(include=[np.number]).columns)
    categorical_columns = list(features.select_dtypes(exclude=[np.number]).columns)
    transformers: list[tuple[str, Any, list[Any]]] = []

    if numeric_columns:
        numeric_pipeline = Pipeline(steps=[("imputer", SimpleImputer(strategy="median"))])
        transformers.append(("numeric", numeric_pipeline, numeric_columns))

    if categorical_columns:
        categorical_pipeline = Pipeline(
            steps=[
                ("imputer", SimpleImputer(strategy="most_frequent")),
                ("one_hot", OneHotEncoder(handle_unknown="ignore")),
            ]
        )
        transformers.append(("categorical", categorical_pipeline, categorical_columns))

    if not transformers:
        raise MLRestrictionError("decision_tree_classifier exige pelo menos uma feature")
    return ColumnTransformer(transformers=transformers)


def decision_tree_classifier(training: TrainingDataset) -> Pipeline:
    """Consume a training dataset and fit the sole supported model."""
    _require_available(training, TrainingDataset, "decision_tree_classifier")
    model = Pipeline(
        steps=[
            ("preprocessor", _preprocessor(training.features)),
            ("classifier", DecisionTreeClassifier(random_state=42)),
        ]
    )
    model.fit(training.features, training.target)
    setattr(model, "_aeon_split_token", training.split_token)
    setattr(model, "_aeon_feature_columns", tuple(training.features.columns.tolist()))
    setattr(model, "_aeon_classes", frozenset(training.target.unique().tolist()))
    _mark_consumed(training)
    return model


@curried
def accuracy(model: Any, testing: TestingDataset) -> float:
    """Consume a compatible held-out test dataset and return bounded accuracy."""
    _require_available(testing, TestingDataset, "accuracy")
    if not isinstance(model, Pipeline):
        raise TypeError(f"accuracy esperava DecisionTreeClassifier, recebeu {type(model).__name__}")
    if getattr(model, "_aeon_split_token", None) is not testing.split_token:
        raise MLRestrictionError("o modelo e o teste têm de vir do mesmo split")

    expected_columns = getattr(model, "_aeon_feature_columns", None)
    actual_columns = tuple(testing.features.columns.tolist())
    if expected_columns != actual_columns:
        raise MLRestrictionError("o schema de features do teste não corresponde ao schema usado no treino")

    expected_classes = getattr(model, "_aeon_classes", None)
    actual_classes = frozenset(testing.target.unique().tolist())
    if expected_classes != actual_classes:
        raise MLRestrictionError("as classes do teste não correspondem às classes usadas no treino")

    score = float(model.score(testing.features, testing.target))
    if not np.isfinite(score) or not 0.0 <= score <= 1.0:
        raise MLRestrictionError(f"accuracy fora do intervalo [0, 1]: {score!r}")
    _mark_consumed(testing)
    return score
