from __future__ import annotations

from typing import Any, Callable, TypeAlias

import numpy as np
import pandas as pd
from sklearn.compose import ColumnTransformer
from sklearn.impute import SimpleImputer
from sklearn.model_selection import train_test_split
from sklearn.pipeline import Pipeline
from sklearn.preprocessing import OneHotEncoder
from sklearn.tree import DecisionTreeClassifier

from aeon.bindings.binding_utils import curried


DataFrame: TypeAlias = pd.DataFrame
Dataset: TypeAlias = tuple[pd.DataFrame, pd.Series]
TrainingDataset: TypeAlias = Dataset
TestingDataset: TypeAlias = Dataset
DatasetSplit: TypeAlias = tuple[TrainingDataset, TestingDataset]


def read_csv(path: str) -> DataFrame:
    """Read a CSV file and retain all of its columns."""
    return pd.read_csv(path)


@curried
def target(df: DataFrame, column: int) -> Dataset:
    """Use the zero-based column as the target and return ``(X, y)``."""
    feature_positions = [position for position in range(len(df.columns)) if position != column]
    features = df.iloc[:, feature_positions].copy()
    target_values = df.iloc[:, column].copy()
    return features, target_values


@curried
def split(ds: Dataset, train_size: float) -> DatasetSplit:
    """Create a deterministic stratified training/testing split."""
    features, target_values = ds
    x_train, x_test, y_train, y_test = train_test_split(
        features,
        target_values,
        train_size=train_size,
        random_state=42,
        stratify=target_values,
    )
    return (x_train, y_train), (x_test, y_test)


@curried
def consume_split(
    parts: DatasetSplit,
    consumer: Callable[[TrainingDataset], Callable[[TestingDataset], Any]],
) -> Any:
    """Pass both linear split halves to an Aeon callback."""
    training, testing = parts
    return consumer(training)(testing)


def _preprocessor(features: pd.DataFrame) -> ColumnTransformer:
    """Build preprocessing that is fitted only as part of training."""
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

    return ColumnTransformer(transformers=transformers)


def decision_tree_classifier(training: TrainingDataset) -> Pipeline:
    """Fit a decision-tree pipeline on the training half."""
    features, target_values = training
    model = Pipeline(
        steps=[
            ("preprocessor", _preprocessor(features)),
            ("classifier", DecisionTreeClassifier(random_state=42)),
        ]
    )
    model.fit(features, target_values)
    return model


@curried
def accuracy(model: Pipeline, testing: TestingDataset) -> float:
    """Evaluate a fitted model on the held-out testing half."""
    features, target_values = testing
    return float(model.score(features, target_values))
