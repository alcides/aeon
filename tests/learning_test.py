"""Type-level pipeline-defect detection in the ``Learning`` library.

These tests exercise the contracts added to ``libraries/Learning.ae`` that
encode the ML-pipeline defects from Pedro Silva's MSc thesis. A *clean*
pipeline type-checks (no errors); a pipeline containing a defect is
rejected by the liquid-type checker.

We drive the full front-end via ``AeonDriver`` so that ``open Learning``
is resolved exactly as it is on the command line, and run with
``no_main=True`` so nothing is executed — we only assert on typing.
"""

from __future__ import annotations

from aeon.facade.driver import AeonDriver, AeonConfig
from aeon.synthesis.uis.api import SilentSynthesisUI


def _typechecks(source: str) -> bool:
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    return not errors


# ─── Clean pipelines — must type-check ──────────────────────────────────


def test_clean_static_pipeline():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 true false false in
        let parts = split ds 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        accuracy model (test_of parts) ;
    """
    assert _typechecks(src)


def test_clean_timeseries_unshuffled_with_f1():
    # A time series split without shuffling, scored with a
    # balance-insensitive metric, is sound.
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 true true false in
        let parts = split ds 0.8 false in
        let model = random_forest_classifier (train_of parts) in
        f1 model (test_of parts) ;
    """
    assert _typechecks(src)


def test_clean_imbalanced_with_f1():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 false false false in
        let parts = split ds 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        f1 model (test_of parts) ;
    """
    assert _typechecks(src)


def test_clean_accuracy_discharged_by_balanced_witness():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 false false false in
        let parts = split ds 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        let test = test_of parts in
        if balanced test then accuracy model test
        else f1 model test ;
    """
    assert _typechecks(src)


def test_clean_regression_per_split_imputation():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 true false true in
        let parts = split ds 0.8 true in
        let train = fill_median (train_of parts) in
        let test = fill_median (test_of parts) in
        let model = ridge train in
        r2 model test ;
    """
    assert _typechecks(src)


def test_clean_csv_path_with_require_enough_data():
    src = """
    open Learning
    def p (path: String) (col: String) : Float =
        let 1 df = read_csv path in
        let ds0 = target df col false false in
        let ds = require_enough_data ds0 in
        let parts = split ds 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        f1 model (test_of parts) ;
    """
    assert _typechecks(src)


# ─── Defective pipelines — must be rejected ─────────────────────────────


def test_defect_temporal_leakage():
    # Shuffling a time series before splitting destroys chronological order.
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 true true false in
        let parts = split ds 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        f1 model (test_of parts) ;
    """
    assert not _typechecks(src)


def test_defect_scale_before_split():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 true false false in
        let scaled = standard_scale ds in
        let parts = split scaled 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        f1 model (test_of parts) ;
    """
    assert not _typechecks(src)


def test_defect_smote_before_split():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 true false false in
        let bds = smote ds in
        let parts = split bds 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        f1 model (test_of parts) ;
    """
    assert not _typechecks(src)


def test_defect_impute_before_split():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 true false true in
        let filled = fill_median ds in
        let parts = split filled 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        f1 model (test_of parts) ;
    """
    assert not _typechecks(src)


def test_defect_evaluate_on_training_set():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 true false false in
        let parts = split ds 0.8 true in
        let train = train_of parts in
        let model = random_forest_classifier train in
        f1 model train ;
    """
    assert not _typechecks(src)


def test_defect_missing_values_to_estimator():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 true false true in
        let parts = split ds 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        f1 model (test_of parts) ;
    """
    assert not _typechecks(src)


def test_defect_lack_of_data():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 20 4 true false false in
        let parts = split ds 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        f1 model (test_of parts) ;
    """
    assert not _typechecks(src)


def test_defect_balance_sensitive_metric_on_imbalanced():
    src = """
    open Learning
    def p (a: Int) : Float =
        let ds = create_dataset 1000 4 false false false in
        let parts = split ds 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        accuracy model (test_of parts) ;
    """
    assert not _typechecks(src)


def test_defect_csv_path_without_require_enough_data():
    # The CSV row count is statically unknown, so the minimum-data
    # precondition of ``split`` cannot be discharged without an assertion.
    src = """
    open Learning
    def p (path: String) (col: String) : Float =
        let 1 df = read_csv path in
        let ds = target df col false false in
        let parts = split ds 0.8 true in
        let model = random_forest_classifier (train_of parts) in
        f1 model (test_of parts) ;
    """
    assert not _typechecks(src)
