"""Minimal runtime bindings for the experimental Aeon ``ML`` library.

This first version intentionally keeps the Aeon types simple.  The fitted
scikit-learn pipeline is still responsible for the practical details needed by
the Titanic data: missing-value imputation and categorical one-hot encoding.
Those transformations are fitted on the training set only.
"""

from __future__ import annotations

from typing import Any

import numpy as np
import pandas as pd
from sklearn.compose import ColumnTransformer
from sklearn.impute import SimpleImputer
from sklearn.model_selection import train_test_split
from sklearn.pipeline import Pipeline
from sklearn.preprocessing import OneHotEncoder
from sklearn.tree import DecisionTreeClassifier

from aeon.bindings.binding_utils import curried


Dataset = tuple[pd.DataFrame, pd.Series]
DatasetSplit = tuple[Dataset, Dataset]


def read_csv(path: str) -> pd.DataFrame:
    """Read all columns from a CSV file."""
    return pd.read_csv(path)


@curried
def target(df: pd.DataFrame, column: int) -> Dataset:
    """Use the column at ``column`` as y and keep the other columns as X."""
    x = df.drop(columns=df.columns[column]).copy()
    y = df.iloc[:, column].copy()
    return (x, y)


@curried
def split(ds: Dataset, train_size: float) -> DatasetSplit:
    """Create a deterministic, stratified train/test split."""
    x, y = ds
    x_train, x_test, y_train, y_test = train_test_split(
        x,
        y,
        train_size=float(train_size),
        random_state=42,
        stratify=y,
    )
    return ((x_train, y_train), (x_test, y_test))


def train_of(parts: DatasetSplit) -> Dataset:
    """Return the training dataset from a split."""
    return parts[0]


def test_of(parts: DatasetSplit) -> Dataset:
    """Return the testing dataset from a split."""
    return parts[1]


def _preprocessor(x: pd.DataFrame) -> ColumnTransformer:
    """Build preprocessing for the numeric and categorical columns in ``x``."""
    numeric_columns = list(x.select_dtypes(include=[np.number]).columns)
    categorical_columns = list(x.select_dtypes(exclude=[np.number]).columns)
    transformers: list[tuple[str, Any, list[str]]] = []

    if numeric_columns:
        numeric_pipeline = Pipeline(
            steps=[
                ("imputer", SimpleImputer(strategy="median")),
            ]
        )
        transformers.append(("numeric", numeric_pipeline, numeric_columns))

    if categorical_columns:
        categorical_pipeline = Pipeline(
            steps=[
                ("imputer", SimpleImputer(strategy="most_frequent")),
                ("one_hot", OneHotEncoder(handle_unknown="ignore")),
            ]
        )
        transformers.append(("categorical", categorical_pipeline, categorical_columns))

    return ColumnTransformer(transformers=transformers)


def decision_tree_classifier(ds: Dataset) -> Pipeline:
    """Fit a decision tree together with its training-only preprocessing."""
    x, y = ds
    model = Pipeline(
        steps=[
            ("preprocessor", _preprocessor(x)),
            ("classifier", DecisionTreeClassifier(random_state=42)),
        ]
    )
    model.fit(x, y)
    return model


@curried
def accuracy(model: Any, ds: Dataset) -> float:
    """Return classification accuracy on a labelled dataset."""
    x, y = ds
    return float(model.score(x, y))
