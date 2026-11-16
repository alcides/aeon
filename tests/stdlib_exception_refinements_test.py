"""Partial native operations require checked input facts; guards remain executable."""

import pytest

from aeon.errors import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def compile_source(source):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    return driver, list(driver.parse(aeon_code=source))


@pytest.mark.parametrize(
    "imports, result, expression",
    [
        ("Buffer", "Int", "Buffer.buf_get (Buffer.buf_alloc 0) 0"),
        ("Array ArrayKernels", "Int", "Array.get (ArrayKernels.map_n_int (fun x => x) (Array.mk_1 7) 10) 9"),
        ("Array Statistics", "Float", "Statistics.quantile (Array.mk_1 1.0) 2.0"),
        ("Array Statistics", "Float", "Statistics.percentile (Array.mk_1 1.0) 101.0"),
        ("Array Statistics", "Float", "Statistics.var (Array.mk_1 1.0)"),
        ("Array Statistics", "Float", "Statistics.std (Array.mk_1 1.0)"),
        ("Tensor", "Vector", "Tensor.normalize (Tensor.vzeros 2)"),
        ("Json", "Int", 'Json.asInt (Json.mkString "x")'),
        ("Json", "Json", 'Json.get Json.mkObject "missing"'),
        ("Json", "Int", "Json.length (Json.mkInt 1)"),
        ("Json", "Json", 'Json.parse "not-json"'),
        ("Contest", "Int", 'Contest.readInt "hello"'),
        ("Contest", "Float", 'Contest.readFloat "hello"'),
        ("Path", "Path", 'Path.withSuffix (Path.mk "a.txt") "txt"'),
        ("Args Array", "Int", 'Args.getInt (Args.parseList (Args.newParser "test") (Array.mk_empty unit)) "missing"'),
        ("Karel", "World", "Karel.world 0 2 0 0 0"),
        ("Karel", "World", "Karel.random_world 2 2 0"),
        ("PropTesting", "Float", "PropTesting.ratio 1 0"),
        ("Random", "Int", "10 / (Random.int_value 1 1 (Random.draw_int 0 0 (Random.new_rng 0)))"),
        ("Image Color", "Float", "Image.diff (Image.mk 1 1 (Color.mk 0 0 0)) (Image.mk 2 2 (Color.mk 0 0 0))"),
        (
            "LearningCore LearningLinear",
            "Unit",
            "LearningCore.dispose_classifier (LearningLinear.logistic_regression (LearningCore.create_dataset 1 1 true false false))",
        ),
        (
            "LearningCore LearningLinear",
            "Unit",
            "LearningCore.dispose_regressor (LearningLinear.linear_regression (LearningCore.create_dataset 0 1 true false false))",
        ),
        (
            "LearningCore LearningNeighbors Tensor",
            "Vector",
            "LearningCore.classify_one (LearningNeighbors.knn_classifier (LearningCore.create_dataset 2 1 true false false)) (Tensor.vzeros 1)",
        ),
        (
            "LearningCore LearningLinear Tensor",
            "Float",
            "LearningCore.regress_one (LearningLinear.linear_regression (LearningCore.create_dataset 4 1 true false false)) (Tensor.vzeros 2)",
        ),
        (
            "LearningCore",
            "Unit",
            "LearningCore.dispose_dataset (LearningCore.train_of (LearningCore.split (LearningCore.create_dataset 11 1 true false false) 0.001 false))",
        ),
        ("PSB2 Array", "Int", "Array.length (PSB2.objective_errors_int (Array.mk_1 1) 2)"),
        ("Math", "Float", "Math.remainder Math.INF 1.0"),
        ("Math", "Float", "Math.sin Math.INF"),
        ("Math", "Int", "Math.toInt Math.INF"),
        ("Math", "Float", "Math.powf 0.0 (0.0 - 1.0)"),
        ("Math", "Float", "Math.lgamma 0.0"),
        (
            "NDArray",
            "Int",
            "NDArray.count (NDArray.iterate (NDArray.full1 2 0) 1 0 (fun step => fun xs => fun output => NDArray.filter output (fun x => false)))",
        ),
    ],
)
def test_invalid_inputs_are_rejected(imports, result, expression):
    source = "\n".join(f"import {m};" for m in imports.split())
    _, errors = compile_source(source + f"\ndef main (_:Int):{result} := {expression};")
    assert any(isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors), errors


@pytest.mark.parametrize(
    "source, expected",
    [
        ("import Json; def main (_:Int):Int := let j := Json.mkInt 7 in if Json.isInt j then Json.asInt j else 0;", 7),
        (
            'import Json; def main (_:Int):Int := let j := Json.setKey Json.mkObject "x" (Json.mkInt 7) in if Json.has j "x" then let v := Json.get j "x" in if Json.isInt v then Json.asInt v else 0 else 0;',
            7,
        ),
        (
            'import Json; def main (_:Int):Int := let s := "7" in if Json.isValid s then let j := Json.parse s in if Json.isInt j then Json.asInt j else 0 else 0;',
            7,
        ),
        (
            'import Contest; def main (_:Int):Int := let s := "42" in if Contest.isInt s then Contest.readInt s else 0;',
            42,
        ),
        ('import String; def main (_:Int):Int := String.stringToInt "²";', -1),
        (
            "import Buffer; def main (_:Int):Int := let b := Buffer.buf_alloc 8 in Buffer.buf_get (Buffer.buf_set b 1 7) 1;",
            7,
        ),
        ("import Statistics; import Array; def main (_:Int):Float := Statistics.var (Array.mk_2 1.0 3.0);", 2.0),
        (
            "import Statistics; import Array; def main (_:Int):Float := Statistics.quantile (Array.mk_2 1.0 3.0) 0.5;",
            2.0,
        ),
        (
            "import Tensor; def main (_:Int):Float := let v := Tensor.vones 2 in if Tensor.norm v > 0.0 then Tensor.norm (Tensor.normalize v) else 0.0;",
            1.0,
        ),
        (
            "import NDArray; def main (_:Int):Int := NDArray.count (NDArray.iterate (NDArray.full1 2 0) 1 0 (fun step => fun xs => fun output => NDArray.map output (fun x => x + 1)));",
            2,
        ),
        (
            'import Path; def main (_:Int):String := let p := Path.mk "a.txt" in if Path.canWithSuffix p ".csv" then Path.toString (Path.withSuffix p ".csv") else "";',
            "a.csv",
        ),
        (
            'import Args; import Array; def main (_:Int):Int := let p := Args.newParser "test" in if Args.canAdd p "count" then let q := Args.addIntOption p "count" 7 "count" in let 1 a := Args.parseList q (Array.mk_empty unit) in let value := if Args.hasInt a "count" then Args.getInt a "count" else 0 in let _ := Args.dispose a in value else 0;',
            7,
        ),
    ],
)
def test_guards_discharge_native_preconditions(source, expected):
    driver, errors = compile_source(source)
    assert not errors, errors
    actual = driver.run()
    assert actual == (pytest.approx(expected) if isinstance(expected, float) else expected)


@pytest.mark.parametrize("separate_predicate_module", [False, True])
def test_imported_unary_predicate_cannot_be_generalized_away(tmp_path, monkeypatch, separate_predicate_module):
    module = tmp_path / "Checked.ae"
    predicate = "def allowed : (x:Int) -> Bool := uninterpreted;\n"
    if separate_predicate_module:
        (tmp_path / "Predicate.ae").write_text(predicate)
        module.write_text('import Predicate; def read (x:{v:Int | Predicate.allowed v}):Int := native "x";')
    else:
        module.write_text(predicate + 'def read (x:{v:Int | allowed v}):Int := native "x";')
    monkeypatch.chdir(tmp_path)
    source = "import Checked; def main (_:Int):Int := Checked.read 0;"
    _, errors = compile_source(source)
    assert any(isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors), errors


def test_csv_shape_claim_is_checked(tmp_path):
    from aeon.bindings import dataframe, machine_learning

    path = tmp_path / "small.csv"
    path.write_text("x\n7\n")
    for binding in (dataframe, machine_learning):
        assert binding.read_csv(str(path), 1, 1).shape == (1, 1)
        with pytest.raises(ValueError, match="CSV row count"):
            binding.read_csv(str(path), 5, 1)
        with pytest.raises(ValueError, match="CSV column count"):
            binding.read_csv(str(path), 1, 2)


def test_cuda_failure_stays_observable_and_disposable():
    from aeon.bindings import cuda

    class FailedPending:
        discarded = False

        def synchronize(self):
            raise cuda.CUDAError("test failure")

        def discard(self):
            self.discarded = True

    pending = FailedPending()
    result = cuda.synchronize_with_status(pending)
    assert not cuda.status_buffer_ok(result)
    assert result.buffer is None and pending.discarded
    cuda.discard_status_buffer(result)
    assert result.status._consumed


def test_empty_learning_datasets_preserve_their_feature_count():
    import pandas as pd
    from aeon.bindings import learning

    generated = learning.Learning_create_dataset(0, 3, True, False, False)
    assert learning.Learning_n_features(generated) == 3
    loaded = learning.Learning_target(pd.DataFrame(columns=["x", "y", "label"]), "label", False, False)
    assert learning.Learning_n_features(loaded) == 2


def test_numeric_column_guard_rejects_nullable_and_complex_cells():
    import pandas as pd
    from aeon.bindings.contracts import numeric_column

    frame = pd.DataFrame({"value": pd.Series([1, pd.NA], dtype="Int64")})
    assert not numeric_column(frame, "value")
    assert not numeric_column(pd.DataFrame({"value": [1j]}), "value")
    assert numeric_column(pd.DataFrame({"value": [1.0, float("nan")]}), "value")


@pytest.mark.parametrize(
    "source",
    [
        """import Cuda; import Array;
def f (d:{v:Device | Cuda.max_allocation v < 4}):Unit :=
    Cuda.free (Cuda.upload_i32 d (Array.mk_1 1));""",
        """import Cuda;
def f (1 pending:(Pending Int)):(StatusPair Int) :=
    Cuda.unpack_status_buffer (Cuda.synchronize_with_status pending);""",
    ],
)
def test_cuda_requires_capacity_and_observed_success(source):
    _, errors = compile_source(source)
    assert any(isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors), errors


def test_dataframe_group_key_and_aggregate_column_must_differ():
    _, errors = compile_source("""import DataFrame;
def bad (1 df:{d:DataFrame | DataFrame.orderableColumn d "x" && DataFrame.numericColumn d "x"}):DataFrame :=
    DataFrame.groupby_agg df "x" "x" "sum";
""")
    assert any(isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors), errors


def test_local_predicate_name_does_not_capture_imported_abstract_parameter():
    driver, errors = compile_source("""import Array;
def p (n:Int):Bool := false;
def main (_:Int):Int := Array.take (Array.mk_1 7) 0;
""")
    assert not errors, errors
    assert driver.run() == 7


def test_dace_search_sentinel_is_safe_only_with_available_storage():
    source = """import Dace;
def c:{v:Column | Dace.size v = 2} := native "[0, 7]";
def main (_:Int):Int := Dace.down_first_nonzero c INDEX;
"""
    driver, errors = compile_source(source.replace("INDEX", "(0 - 1)"))
    assert not errors, errors
    assert driver.run() == 7
    _, errors = compile_source(source.replace("INDEX", "(0 - 3)"))
    assert any(isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors), errors
