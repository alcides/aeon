"""
!!! THIS DOCUMENT WAS AI GENERATED !!! 

The objective is a quick Runtime and end-to-end tests 
for the linear ``ML`` library.

The Aeon types reject resource reuse statically.  These tests call the Python
binding directly as well, both to exercise its data validation and to verify
that the same ownership protocol is defended at the FFI boundary.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pandas as pd
import pytest
from sklearn.pipeline import Pipeline

from aeon.bindings import machine_learning as ml


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]


def _classification_frame() -> pd.DataFrame:
    """Return a small, learnable three-class frame with mixed features."""
    labels = [0] * 6 + [1] * 6 + [2] * 6
    return pd.DataFrame(
        {
            "row_id": range(18),
            "label": labels,
            "signal": list(range(6)) + list(range(10, 16)) + list(range(20, 26)),
            "group": ["low"] * 6 + ["middle"] * 6 + ["high"] * 6,
            # Missing feature values are supported by the training-only
            # preprocessing pipeline; missing target values are not.
            "optional": [None if index % 4 == 0 else float(index) for index in range(18)],
        }
    )


def _owned_dataset(frame: pd.DataFrame | None = None) -> tuple[ml.DataFrame, ml.Dataset]:
    source = ml.DataFrame((frame if frame is not None else _classification_frame()).copy())
    return source, ml.target(source, 1)


def _write_frame(tmp_path: Path, frame: pd.DataFrame, name: str = "dataset.csv") -> Path:
    path = tmp_path / name
    frame.to_csv(path, index=False)
    return path


def test_read_csv_returns_a_fresh_validated_dataframe(tmp_path: Path):
    expected = _classification_frame()
    path = _write_frame(tmp_path, expected)

    actual = ml.read_csv(str(path))

    assert isinstance(actual, ml.DataFrame)
    assert not actual._consumed
    pd.testing.assert_frame_equal(actual.value, expected)


@pytest.mark.parametrize(
    ("row_count", "column_count", "message"),
    [
        (3, 2, "pelo menos 4 linhas"),
        (4, 1, "pelo menos uma feature"),
    ],
)
def test_read_csv_rejects_frames_that_cannot_form_a_dataset(
    tmp_path: Path,
    row_count: int,
    column_count: int,
    message: str,
):
    frame = pd.DataFrame({f"column_{column}": range(row_count) for column in range(column_count)})
    path = _write_frame(tmp_path, frame)

    with pytest.raises(ml.MLRestrictionError, match=message):
        ml.read_csv(str(path))


def test_read_csv_rejects_duplicate_column_names(tmp_path: Path):
    path = tmp_path / "duplicate_headers.csv"
    path.write_text(
        "feature,label,feature\n0,0,a\n1,0,b\n2,1,c\n3,1,d\n",
        encoding="utf-8",
    )

    with pytest.raises(ml.MLRestrictionError, match="colunas.*(únicos|duplicados)"):
        ml.read_csv(str(path))


@pytest.mark.parametrize("column", [-1, 5])
def test_target_rejects_an_out_of_bounds_column_without_consuming_the_frame(column: int):
    source = ml.DataFrame(_classification_frame())

    with pytest.raises(ml.MLRestrictionError, match="fora do intervalo"):
        ml.target(source, column)

    assert not source._consumed


@pytest.mark.parametrize("column", [True, 1.0, "1", None])
def test_target_rejects_a_non_integer_column_without_consuming_the_frame(column: Any):
    source = ml.DataFrame(_classification_frame())

    with pytest.raises(TypeError, match="target.*Int"):
        ml.target(source, column)

    assert not source._consumed


def test_target_rejects_missing_labels_without_consuming_the_frame():
    frame = _classification_frame()
    frame.loc[3, "label"] = None
    source = ml.DataFrame(frame)

    with pytest.raises(ml.MLRestrictionError, match="target.*em falta"):
        ml.target(source, 1)

    assert not source._consumed


def test_target_rejects_a_single_class_without_consuming_the_frame():
    frame = _classification_frame()
    frame["label"] = 0
    source = ml.DataFrame(frame)

    with pytest.raises(ml.MLRestrictionError, match="pelo menos duas classes"):
        ml.target(source, 1)

    assert not source._consumed


def test_target_rejects_a_rare_class_without_consuming_the_frame():
    frame = _classification_frame()
    frame["label"] = [0] * 17 + [1]
    source = ml.DataFrame(frame)

    with pytest.raises(ml.MLRestrictionError, match="duas linhas por classe"):
        ml.target(source, 1)

    assert not source._consumed


def test_target_removes_the_label_column_and_consumes_the_dataframe():
    source = ml.DataFrame(_classification_frame())

    dataset = ml.target(source, 1)

    assert source._consumed
    assert "label" not in dataset.features.columns
    assert dataset.target.name == "label"
    assert len(dataset.features.columns) == 4
    assert len(dataset.target) == 18


@pytest.mark.parametrize(
    "fraction",
    [0.0, 1.0, -0.01, 1.01, float("nan"), float("inf"), float("-inf")],
)
def test_split_rejects_an_out_of_range_or_non_finite_fraction_without_consuming_dataset(fraction: float):
    _, dataset = _owned_dataset()

    with pytest.raises(ml.MLRestrictionError, match="0.0 < f < 1.0"):
        ml.split(dataset, fraction)

    assert not dataset._consumed


@pytest.mark.parametrize("fraction", [True, "0.7", None])
def test_split_rejects_a_non_float_fraction_without_consuming_dataset(fraction: Any):
    _, dataset = _owned_dataset()

    with pytest.raises(TypeError, match="train_size.*Float"):
        ml.split(dataset, fraction)

    assert not dataset._consumed


def test_split_rejects_a_fraction_too_small_to_preserve_every_class():
    _, dataset = _owned_dataset()

    with pytest.raises(ml.MLRestrictionError, match="split estratificado"):
        ml.split(dataset, 0.1)

    assert not dataset._consumed


def test_split_is_deterministic_disjoint_and_preserves_every_class():
    _, first_dataset = _owned_dataset()
    _, second_dataset = _owned_dataset()

    first = ml.split(first_dataset, 2.0 / 3.0)
    second = ml.split(second_dataset, 2.0 / 3.0)

    assert first_dataset._consumed
    assert second_dataset._consumed
    assert first.training.features.index.tolist() == second.training.features.index.tolist()
    assert first.testing.features.index.tolist() == second.testing.features.index.tolist()
    assert set(first.training.features.index).isdisjoint(first.testing.features.index)
    assert len(first.training.features) + len(first.testing.features) == len(_classification_frame())
    assert set(first.training.target) == {0, 1, 2}
    assert set(first.testing.target) == {0, 1, 2}
    assert first.training.split_token is first.testing.split_token
    assert first.training.split_token is not second.training.split_token


def test_every_linear_runtime_resource_can_be_consumed_only_once():
    source, dataset = _owned_dataset()
    parts = ml.split(dataset, 2.0 / 3.0)
    captured: dict[str, Any] = {}

    def train_and_evaluate(training: ml.TrainingDataset):
        captured["training"] = training

        def evaluate(testing: ml.TestingDataset) -> float:
            captured["testing"] = testing
            model = ml.decision_tree_classifier(training)
            captured["model"] = model
            return ml.accuracy(model, testing)

        return evaluate

    score = ml.consume_split(parts, train_and_evaluate)
    training = captured["training"]
    testing = captured["testing"]
    model = captured["model"]

    assert 0.0 <= score <= 1.0
    assert source._consumed
    assert dataset._consumed
    assert parts._consumed
    assert training._consumed
    assert testing._consumed

    with pytest.raises(ml.MLResourceConsumedError, match="DataFrame"):
        ml.target(source, 1)
    with pytest.raises(ml.MLResourceConsumedError, match="Dataset"):
        ml.split(dataset, 2.0 / 3.0)
    with pytest.raises(ml.MLResourceConsumedError, match="DatasetSplit"):
        ml.consume_split(parts, train_and_evaluate)
    with pytest.raises(ml.MLResourceConsumedError, match="TrainingDataset"):
        ml.decision_tree_classifier(training)
    with pytest.raises(ml.MLResourceConsumedError, match="TestingDataset"):
        ml.accuracy(model, testing)


def test_consume_split_rejects_a_callback_that_abandons_the_testing_half():
    _, dataset = _owned_dataset()
    parts = ml.split(dataset, 2.0 / 3.0)

    def train_only(training: ml.TrainingDataset):
        def abandon_testing(_testing: ml.TestingDataset) -> Pipeline:
            return ml.decision_tree_classifier(training)

        return abandon_testing

    with pytest.raises(ml.MLRestrictionError, match="não consumiu.*TestingDataset"):
        ml.consume_split(parts, train_only)

    assert parts._consumed
    assert parts.training._consumed
    assert not parts.testing._consumed


def test_decision_tree_training_and_accuracy_support_mixed_missing_features():
    _, dataset = _owned_dataset()
    parts = ml.split(dataset, 2.0 / 3.0)
    captured: dict[str, Any] = {}

    def train_and_evaluate(training: ml.TrainingDataset):
        def evaluate(testing: ml.TestingDataset) -> float:
            model = ml.decision_tree_classifier(training)
            captured["model"] = model
            return ml.accuracy(model, testing)

        return evaluate

    score = ml.consume_split(parts, train_and_evaluate)

    assert isinstance(captured["model"], Pipeline)
    assert captured["model"].named_steps["classifier"].__class__.__name__ == "DecisionTreeClassifier"
    assert score == pytest.approx(1.0)


def test_accuracy_rejects_test_data_from_another_split_without_consuming_it():
    _, first_dataset = _owned_dataset()
    _, second_dataset = _owned_dataset()
    first = ml.split(first_dataset, 2.0 / 3.0)
    second = ml.split(second_dataset, 2.0 / 3.0)
    first_model = ml.decision_tree_classifier(first.training)

    with pytest.raises(ml.MLRestrictionError, match="mesmo split"):
        ml.accuracy(first_model, second.testing)

    assert not second.testing._consumed
    assert 0.0 <= ml.accuracy(first_model, first.testing) <= 1.0
    second_model = ml.decision_tree_classifier(second.training)
    assert 0.0 <= ml.accuracy(second_model, second.testing) <= 1.0


def test_accuracy_rejects_an_incompatible_feature_schema_without_consuming_test():
    _, dataset = _owned_dataset()
    parts = ml.split(dataset, 2.0 / 3.0)
    model = ml.decision_tree_classifier(parts.training)
    parts.testing.features = parts.testing.features.drop(columns=["optional"])

    with pytest.raises(ml.MLRestrictionError, match="schema de features"):
        ml.accuracy(model, parts.testing)

    assert not parts.testing._consumed


def test_accuracy_rejects_incompatible_classes_without_consuming_test():
    _, dataset = _owned_dataset()
    parts = ml.split(dataset, 2.0 / 3.0)
    model = ml.decision_tree_classifier(parts.training)
    parts.testing.target = parts.testing.target.replace({2: 1})

    with pytest.raises(ml.MLRestrictionError, match="classes do teste"):
        ml.accuracy(model, parts.testing)

    assert not parts.testing._consumed


def test_titanic_example_runs_end_to_end():
    runner = REPOSITORY_ROOT / "examples" / "machine_learning" / "run_titanic.py"
    completed = subprocess.run(
        [sys.executable, str(runner)],
        cwd=REPOSITORY_ROOT,
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )

    assert completed.returncode == 0, completed.stderr
    result = re.search(r"Accuracy.+?:\s*([0-9]+(?:\.[0-9]+)?)%", completed.stdout)
    assert result is not None, completed.stdout
    assert 0.0 <= float(result.group(1)) <= 100.0
