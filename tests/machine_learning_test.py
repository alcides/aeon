"""Static contract tests for the refinement-typed ``ML`` library."""

from __future__ import annotations

from pathlib import Path

import pytest

from aeon.facade.api import (
    LinearTypeNotBoundLinearlyError,
    LinearUnusedError,
    LinearUsedTooManyTimesError,
    LiquidTypeCheckingFailedRelation,
    UnificationSubtypingError,
)
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
RESTRICTIONS_DIR = REPOSITORY_ROOT / "examples" / "machine_learning" / "restrictions"
TITANIC_PROGRAM = REPOSITORY_ROOT / "examples" / "machine_learning" / "titanic_dataset.ae"

VALID_EXAMPLES = tuple(sorted(RESTRICTIONS_DIR.glob("*_valid.ae")))
INVALID_EXAMPLES: dict[str, type[Exception]] = {
    "00_linear_type_invalid.ae": LinearTypeNotBoundLinearlyError,
    "01_dataframe_target_invalid.ae": LinearUsedTooManyTimesError,
    "02_dataset_split_invalid.ae": LinearUsedTooManyTimesError,
    "03_datasetsplit_consume_invalid.ae": LinearUsedTooManyTimesError,
    "04_training_train_invalid.ae": LinearUsedTooManyTimesError,
    "05_testing_accuracy_invalid.ae": LinearUsedTooManyTimesError,
    "06_split_fraction_invalid.ae": LiquidTypeCheckingFailedRelation,
    "07_target_index_invalid.ae": LiquidTypeCheckingFailedRelation,
    "08_train_test_roles_invalid.ae": UnificationSubtypingError,
    "09_linear_resource_used_invalid.ae": LinearUnusedError,
    "10_accuracy_bounds_invalid.ae": LiquidTypeCheckingFailedRelation,
    "11_feature_compatibility_invalid.ae": LiquidTypeCheckingFailedRelation,
    "12_target_metadata_invalid.ae": LiquidTypeCheckingFailedRelation,
    "13_split_provenance_invalid.ae": LiquidTypeCheckingFailedRelation,
}


def _parse(path: Path, *, no_main: bool = True) -> tuple[AeonDriver, list[Exception]]:
    setup_logger()
    config = AeonConfig(
        synthesizer="none",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=no_main,
        contracts=False,
    )
    driver = AeonDriver(config)
    return driver, list(driver.parse(filename=str(path)))


def _parse_source(source: str) -> list[Exception]:
    setup_logger()
    config = AeonConfig(
        synthesizer="none",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
        contracts=False,
    )
    return list(AeonDriver(config).parse(aeon_code=source))


def test_static_examples_are_paired_and_all_invalid_cases_are_registered():
    valid_cases = {path.name.removesuffix("_valid.ae") for path in RESTRICTIONS_DIR.glob("*_valid.ae")}
    invalid_paths = tuple(RESTRICTIONS_DIR.glob("*_invalid.ae"))
    invalid_cases = {path.name.removesuffix("_invalid.ae") for path in invalid_paths}

    assert valid_cases == invalid_cases
    assert {path.name for path in invalid_paths} == set(INVALID_EXAMPLES)


@pytest.mark.parametrize("path", VALID_EXAMPLES, ids=lambda path: path.stem)
def test_valid_static_restriction(path: Path):
    _, errors = _parse(path)

    assert errors == []


@pytest.mark.parametrize(
    ("filename", "expected_error"),
    INVALID_EXAMPLES.items(),
    ids=[Path(filename).stem for filename in INVALID_EXAMPLES],
)
def test_invalid_static_restriction(filename: str, expected_error: type[Exception]):
    _, errors = _parse(RESTRICTIONS_DIR / filename)

    assert len(errors) == 1
    assert isinstance(errors[0], expected_error), errors


@pytest.mark.parametrize(
    "resource_type",
    ("DataFrame", "Dataset", "DatasetSplit", "TrainingDataset", "TestingDataset"),
)
def test_every_ml_resource_type_requires_a_linear_binder(resource_type: str):
    errors = _parse_source(
        f"""
        open ML
        def invalid (resource: {resource_type}) : Int := 0
        """
    )

    assert any(isinstance(error, LinearTypeNotBoundLinearlyError) for error in errors), errors


@pytest.mark.parametrize("fraction", ("0.0", "-0.1"))
def test_split_rejects_non_positive_static_fractions(fraction: str):
    errors = _parse_source(
        f"""
        open ML
        def invalid (1 dataset: {{ds: Dataset | ds_features ds >= 1}}) : DatasetSplit :=
            split dataset {fraction}
        """
    )

    assert any(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors), errors


def test_target_rejects_a_negative_static_index():
    errors = _parse_source(
        """
        open ML
        def invalid (1 df: {table: DataFrame | df_cols table = 12}) : Dataset :=
            target df (0 - 1)
        """
    )

    assert any(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors), errors


def test_accuracy_rejects_training_data():
    errors = _parse_source(
        """
        open ML
        def invalid (model: DecisionTreeClassifier) (1 training: TrainingDataset) : Float :=
            accuracy model training
        """
    )

    assert any(isinstance(error, UnificationSubtypingError) for error in errors), errors


def test_titanic_pipeline_runs_end_to_end():
    driver, errors = _parse(TITANIC_PROGRAM, no_main=False)

    assert errors == []
    result = driver.run()
    assert not isinstance(result, bool)
    assert isinstance(result, (int, float))
    assert 0.0 <= float(result) <= 1.0
