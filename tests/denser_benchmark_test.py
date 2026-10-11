"""The DENSER grammar is an Aeon synthesis problem, not a Python search space."""

import json

from hypothesis import given, strategies as st
import numpy as np
import pytest

from aeon.benchmarks.denser import (
    CONSTRUCTORS,
    DenserBenchmark,
    SOURCE_COMMIT,
    TASK_DIR,
    build_model,
    decode,
    load_data,
    optimizer,
    parameter_count,
    train_and_score,
)


def candidate(dataset=0, learner="sgd", act=1, kind=1, padding=1, stride=1, kernel=3):
    side = 28 if dataset == 0 else 32
    out = (side + stride - 1) // stride if padding else (side - kernel) // stride + 1
    conv = f"Denser.conv (Denser.input {dataset}) 32 {kernel} {stride} {padding} {act} true {out}"
    pool = f"Denser.pool ({conv}) {kind} 2 2 0 {(out - 2) // 2 + 1}"
    head = f"Denser.softmax (Denser.dense (Denser.flatten ({pool})) 128 {act} true)"
    args = {"sgd": "0.01 0.9 0.0001 false", "adam": "0.01 0.9 0.99 0.0001", "rmsprop": "0.01 0.9 0.0001"}[learner]
    return f"Denser.{learner} ({head}) {args} 5 50"


def value(dataset=0, learner="sgd", act=1, kind=1, padding=1, stride=1, kernel=3):
    side = 28 if dataset == 0 else 32
    out = (side + stride - 1) // stride if padding else (side - kernel) // stride + 1
    conv = ("Denser_conv", ("Denser_input", dataset), 32, kernel, stride, padding, act, True, out)
    pool = ("Denser_pool", conv, kind, 2, 2, 0, (out - 2) // 2 + 1)
    head = ("Denser_softmax", ("Denser_dense", ("Denser_flatten", pool), 128, act, True))
    args = {"sgd": (0.01, 0.9, 0.0001, False), "adam": (0.01, 0.9, 0.99, 0.0001), "rmsprop": (0.01, 0.9, 0.0001)}[
        learner
    ]
    return (f"Denser_{learner}", head, *args, 5, 50)


@pytest.fixture(scope="module")
def benchmark():
    return DenserBenchmark("mnist")


@pytest.fixture
def data(tmp_path):
    # Deliberately synthetic, tiny integration fixture. Never reported as MNIST results.
    rng = np.random.default_rng(42)
    path = tmp_path / "smoke.npz"
    np.savez_compressed(
        path,
        X_train=rng.normal(size=(4, 1, 28, 28)).astype(np.float32),
        y_train=np.array([0, 1, 2, 3], dtype=np.int64),
        X_valid=rng.normal(size=(3, 1, 28, 28)).astype(np.float32),
        y_valid=np.array([0, 1, 2], dtype=np.int64),
    )
    return path


def test_provenance_and_grammar_coverage():
    manifest = json.loads((TASK_DIR / "provenance.json").read_text())
    assert manifest["commit"] == SOURCE_COMMIT
    assert set(manifest["constructors"]) == CONSTRUCTORS
    source = (TASK_DIR / "Denser.ae").read_text()
    assert "native" not in source and "axiom" not in source and "?" not in source
    for constructor in CONSTRUCTORS:
        assert f"| {constructor} " in source
    for task in ("mnist", "cifar10", "smoke"):
        text = (TASK_DIR / f"{task}.ae").read_text()
        assert text.count("?architecture") == 1
        assert "@maximize_float" in text and "@minimize_int" in text


@pytest.mark.parametrize("learner", ["sgd", "adam", "rmsprop"])
def test_aeon_controls_compile_and_execute(benchmark, learner):
    expression = candidate(learner=learner)
    assert benchmark.verify(expression)
    actual = benchmark.value(expression)
    assert actual == value(learner=learner)
    assert parameter_count(actual) == 804554


def test_cifar10_shape_and_dataset_refinement():
    benchmark = DenserBenchmark("cifar10")
    assert benchmark.verify(candidate(dataset=1, act=0, kind=0, padding=0, stride=3, kernel=5))
    assert not benchmark.verify(candidate(dataset=0))


@pytest.mark.parametrize(
    "replacement",
    [
        ("32 3 1 1 1 true 28", "31 3 1 1 1 true 28"),
        ("32 3 1 1 1 true 28", "32 6 1 1 1 true 28"),
        ("32 3 1 1 1 true 28", "32 3 0 1 1 true 28"),
        ("32 3 1 1 1 true 28", "32 3 1 1 1 true 27"),
        ("128 1 true", "127 1 true"),
        ("0.01 0.9 0.0001 false 5 50", "0.2 0.9 0.0001 false 5 50"),
        ("0.01 0.9 0.0001 false 5 50", "0.01 0.9 0.0001 false 4 50"),
        ("0.01 0.9 0.0001 false 5 50", "0.01 0.9 0.0001 false 5 501"),
    ],
)
def test_invalid_parameters_and_shape_witnesses_are_rejected_by_aeon(benchmark, replacement):
    before, after = replacement
    assert not benchmark.verify(candidate().replace(before, after))


@pytest.mark.parametrize(
    "expression",
    [
        "Denser.input 0",
        "Denser.flatten (Denser.input 0)",
        "Denser.softmax (Denser.input 0)",
        "Denser.sgd (Denser.input 0) 0.01 0.9 0.0001 false 5 50",
        "experiment",
        'native "42"',
        "?other",
        "Denser.rec",
        "let x := 1 in x",
        "(",
    ],
)
def test_incomplete_or_out_of_grammar_candidates_never_reach_training(benchmark, expression):
    assert not benchmark.verify(expression)


def test_optimizer_endpoint_one_is_rejected(benchmark):
    assert not benchmark.verify(candidate(learner="adam").replace("0.9 0.99", "1.0 0.99"))
    assert not benchmark.verify(candidate(learner="rmsprop").replace("0.01 0.9", "0.01 1.0"))


@pytest.mark.parametrize("learner", ["sgd", "adam", "rmsprop"])
def test_tensor_models_and_optimizers_match_the_encoding(learner):
    torch = pytest.importorskip("torch")
    torch.set_num_threads(1)
    encoding = decode(value(learner=learner, act=0, kind=0, padding=1, stride=3, kernel=4))
    model = build_model(encoding)
    output = model(torch.zeros(2, 1, 28, 28))
    assert output.shape == (2, 10)
    assert torch.allclose(output.sum(1), torch.ones(2))
    assert sum(p.numel() for p in model.parameters()) == encoding.parameters
    assert optimizer(model, encoding.learning).param_groups[0]["lr"] == 0.01


@given(
    dataset=st.integers(0, 1),
    act=st.integers(0, 2),
    kind=st.integers(0, 1),
    padding=st.integers(0, 1),
    stride=st.integers(1, 3),
    kernel=st.integers(2, 5),
)
def test_numerical_boundary_obeys_dimension_equations(dataset, act, kind, padding, stride, kernel):
    encoding = decode(value(dataset=dataset, act=act, kind=kind, padding=padding, stride=stride, kernel=kernel))
    side = 28 if dataset == 0 else 32
    out = (side + stride - 1) // stride if padding else (side - kernel) // stride + 1
    pooled = (out - 2) // 2 + 1
    channels = 1 if dataset == 0 else 3
    expected = 32 * (channels * kernel * kernel + 1) + 128 * (32 * pooled * pooled + 1) + 10 * 129
    assert encoding.parameters == expected


def test_decoder_rejects_invalid_shape_witness_and_unknown_node():
    raw = value()
    conv = raw[1][1][1][1][1]
    assert conv[0] == "Denser_conv"
    broken = (*conv[:-1], 27)
    pool = ("Denser_pool", broken, 1, 2, 2, 0, 14)
    head = ("Denser_softmax", ("Denser_dense", ("Denser_flatten", pool), 128, 1, True))
    with pytest.raises(ValueError, match="dimension"):
        decode(("Denser_sgd", head, 0.01, 0.9, 0.0001, False, 5, 50))
    with pytest.raises(ValueError):
        decode(("arbitrary",))


def test_training_is_real_reproducible_and_resource_bounded(data):
    pytest.importorskip("torch")
    first = train_and_score(value(), data, epochs=1)
    assert first == train_and_score(value(), data, epochs=1)
    assert first in (0.0, 1 / 3, 2 / 3, 1.0)
    with pytest.raises(ValueError, match="parameter cap"):
        train_and_score(value(), data, max_parameters=100)
    with pytest.raises(ValueError):
        train_and_score(value(), data, epochs=401)


def test_validation_data_contract(data, tmp_path):
    assert load_data(data, 0)[0].shape == (4, 1, 28, 28)
    with pytest.raises(ValueError):
        load_data(data, 1)
    invalid = tmp_path / "invalid.npz"
    np.savez(invalid, X_test=np.zeros((1, 1, 28, 28)))
    with pytest.raises(ValueError, match="only"):
        load_data(invalid, 0)


def test_missing_dataset_is_not_silently_replaced_with_fake_fitness(monkeypatch):
    from aeon.benchmarks.denser import accuracy

    monkeypatch.delenv("DENSER_DATA", raising=False)
    with pytest.raises(ValueError, match="no synthetic"):
        accuracy(value())


def test_mixed_goal_directions_and_synthesis_scope(benchmark):
    goals = benchmark.metadata[benchmark.function]["goals"]
    assert [g.minimize for g in goals] == [False, True]
    assert all(g.length == 1 for g in goals)
    names = {n.name for n, _ in benchmark.ctx.vars()}
    assert {f"Denser_{c}" for c in CONSTRUCTORS} <= names
    assert not names & {"experiment", "accuracy", "parameters", "native", "Denser_rec"}


def test_search_rejects_invalid_configuration_before_evaluating_candidates(benchmark, data):
    for budget in (0, -1, float("nan"), float("inf")):
        with pytest.raises(ValueError, match="Budget"):
            benchmark.synthesize(data, budget=budget)
    with pytest.raises(ValueError):
        benchmark.synthesize(data, epochs=401)
    with pytest.raises(FileNotFoundError):
        benchmark.synthesize(data.parent / "missing.npz")


def test_actual_aeon_synthesis_completes_bounded_smoke_task(data):
    pytest.importorskip("torch")
    benchmark = DenserBenchmark("smoke")
    result = benchmark.synthesize(data, backend="enumerative", budget=1)
    assert result is not None
    assert benchmark.verify(result["candidate"])
    assert result["parameters"] == 804554
    assert 0 <= result["validation_accuracy"] <= 1
    assert result["source_commit"] == SOURCE_COMMIT
