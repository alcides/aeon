"""Published-format imports are exhaustive, embedded, isolated and leak-free."""

from dataclasses import replace
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import zipfile

import pytest

from aeon.benchmarks import karel as dataset
from aeon.benchmarks.karel_runner import run_task, run_isolated
from aeon.bindings import karel as k


ROOT = Path(__file__).resolve().parent.parent


def grid_json(w):
    return {
        "rows": w.height,
        "cols": w.width,
        "hero": f"{w.height - 1 - w.y}:{w.x}:{('north', 'east', 'south', 'west')[w.facing]}",
        "blocked": " ".join(f"{w.height - 1 - y}:{x}" for x, y in sorted(w.walls)),
        "markers": " ".join(f"{w.height - 1 - y}:{x}:{n}" for x, y, n in w.markers),
    }


def sparse_tensor(w):
    cells = set()

    def add(channel, row, col):
        cells.add(channel * 18 * 18 + row * 18 + col)

    for row in range(w.height + 2):
        for col in range(w.width + 2):
            if row in (0, w.height + 1) or col in (0, w.width + 1):
                add(5, row, col)
    add(w.facing, w.height - w.y, w.x + 1)
    for x, y in w.walls:
        add(4, w.height - y, x + 1)
    for x, y, n in w.markers:
        add(5 + n, w.height - y, x + 1)
    return " ".join(f"{index}:1" for index in sorted(cells))


def source_record(tokens=None, program=k.move):
    examples = []
    for y in range(6):
        initial = k.with_wall(k.world(5, 6, 1, y, 1), 4, y)
        initial = k.with_markers(initial, 1, y, 2)
        expected = program(initial)
        examples.append(
            {
                "inpgrid_json": grid_json(initial),
                "outgrid_json": grid_json(expected),
                "inpgrid_tensor": sparse_tensor(initial),
                "outgrid_tensor": sparse_tensor(expected),
            }
        )
    return {
        "guid": "fixture-not-a-published-task",
        "program_tokens": tokens or ["DEF", "run", "m(", "move", "m)"],
        "examples": examples,
    }


@pytest.mark.parametrize("facing", range(4))
def test_published_world_formats_have_correct_coordinates_and_direction(facing):
    world = k.with_wall(k.world(4, 3, 1, 0, facing), 3, 2)
    world = k.with_markers(world, 2, 1, 10)
    assert dataset.from_grid_json(grid_json(world)) == world
    decoded = dataset.from_sparse_tensor(sparse_tensor(world))
    assert decoded == world and decoded.strict and decoded.marker_limit == 101
    assert decoded.y == 0


def test_old_published_json_world_format():
    grid = {
        "rows": 3,
        "cols": 4,
        "heroRow": 2,
        "heroCol": 1,
        "heroDir": "south",
        "blocked": ["....", "...*", "...."],
        "markers": [{"r": 1, "c": 2, "num": 3}],
    }
    w = dataset.from_grid_json(grid)
    assert (w.x, w.y, w.facing) == (1, 0, 2)
    assert w.walls == frozenset({(3, 1)}) and k.marker_count_at(w, 2, 1) == 3


def test_bad_published_tensors_and_conflicting_formats_are_rejected():
    w = k.world(4, 3, 1, 1, 1)
    valid = sparse_tensor(w)
    for invalid in ("", valid + " 6000:1", valid + " " + valid.split()[0], valid.replace(":1", ":2", 1)):
        with pytest.raises(ValueError):
            dataset.from_sparse_tensor(invalid)
    example = source_record()["examples"][0]
    example["outgrid_json"] = example["inpgrid_json"]
    with pytest.raises(ValueError, match="disagree"):
        dataset.decode_example(example)


def test_original_jsonl_is_lazy_and_loadable_through_library(tmp_path):
    path = tmp_path / "test.json"
    path.write_text("\n" + json.dumps(source_record()) + "\n", encoding="utf-8")
    loaded = k.load_examples(str(path))
    assert isinstance(loaded, dataset.JsonlDataset) and len(loaded) == 1
    assert len(loaded[0]) == 6 and k.fitness(k.move, loaded[0]) == 0
    assert list(loaded.offsets) == [1]
    with pytest.raises(IndexError):
        loaded[-1]


def test_validation_fetch_is_pinned_and_extracts_only_known_data(tmp_path, monkeypatch):
    data = (json.dumps(source_record()) + "\n").encode()
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w") as archive:
        archive.writestr("val.json", data)
    archive_data = buffer.getvalue()
    monkeypatch.setattr(dataset, "VALIDATION_ARCHIVE_SHA256", hashlib.sha256(archive_data).hexdigest())
    monkeypatch.setattr(dataset, "VALIDATION_JSONL_SHA256", hashlib.sha256(data).hexdigest())
    monkeypatch.setattr(dataset.urllib.request, "urlopen", lambda *args, **kwargs: io.BytesIO(archive_data))
    destination = tmp_path / "recovered"
    provenance = dataset.fetch_validation(destination)
    assert (destination / "val.json").read_bytes() == data
    assert not provenance["full_corpus"] and provenance["missing_splits"] == ["train", "test"]
    with pytest.raises(FileExistsError):
        dataset.fetch_validation(destination)
    monkeypatch.setattr(dataset, "VALIDATION_ARCHIVE_SHA256", "invalid")
    with pytest.raises(ValueError, match="SHA-256 mismatch"):
        dataset.fetch_validation(tmp_path / "bad-hash")
    assert not (tmp_path / "bad-hash/val.json").exists()


def test_parallel_runner_is_ordered_and_streaming(monkeypatch):
    from aeon.benchmarks import karel_runner as runner

    consumed = []

    def payloads():
        for index in range(10):
            consumed.append(index)
            yield {"observed": {"id": index, "guid": str(index)}}

    monkeypatch.setattr(runner, "run_isolated", lambda *args: {"status": "ok"})
    results = runner.isolated_results(payloads(), 2, 1)
    first = next(results)
    assert first["id"] == 0 and len(consumed) == 2
    assert [first["id"], *(result["id"] for result in results)] == list(range(10))


def test_import_preserves_all_tasks_examples_and_separates_labels(tmp_path):
    source = tmp_path / "train.json.gz"
    with gzip.open(source, "wt", encoding="utf-8") as stream:
        for index in range(17):
            record = source_record()
            record["guid"] = f"fixture-{index}"
            record["program_json"] = {"run": [{"type": "move"}]}
            for example_index, example in enumerate(record["examples"]):
                example["example_index"] = example_index
                example["actions"] = ["move"]
            stream.write(json.dumps(record) + "\n")
    out = tmp_path / "imported"
    manifest = dataset.import_split(source, out)
    assert manifest["tasks"] == 17 and manifest["heldout_examples"] == 1
    observed = dataset.JsonlDataset(str(out / "observed.jsonl"))
    heldout = dataset.JsonlDataset(str(out / "heldout.jsonl"))
    references = dataset.JsonlDataset(str(out / "references.jsonl"))
    assert len(observed) == len(heldout) == len(references) == 17
    for index in range(17):
        assert len(observed[index]) == 5 and len(heldout[index]) == 1
        assert observed.record(index)["guid"] == f"fixture-{index}"
        assert "expression" not in observed.record(index) and "program_tokens" not in observed.record(index)
        assert "actions" not in observed.record(index)
        assert references.record(index)["program_json"] == {"run": [{"type": "move"}]}
        assert references.record(index)["examples_metadata"][5] == {"example_index": 5, "actions": ["move"]}
        assert k.fitness(k.move, observed[index] + heldout[index]) == 0
    with pytest.raises(FileExistsError):
        dataset.import_split(source, out)


@pytest.mark.parametrize("mutation", ["few_examples", "bad_code", "bad_world"])
def test_import_never_skips_bad_records_or_claims_completion(tmp_path, mutation):
    record = source_record()
    if mutation == "few_examples":
        record["examples"].pop()
    elif mutation == "bad_code":
        record["program_tokens"] = ["DEF", "run", "m(", "unknown", "m)"]
    else:
        record["examples"][0]["inpgrid_json"]["hero"] = "100:0:east"
    source = tmp_path / "train.json"
    source.write_text(json.dumps(source_record()) + "\n" + json.dumps(record) + "\n", encoding="utf-8")
    out = tmp_path / "imported"
    with pytest.raises(ValueError, match=":2:"):
        dataset.import_split(source, out)
    assert not (out / "manifest.json").exists()


@pytest.mark.parametrize(
    "tokens,expected",
    [
        (["turnLeft", "turnRight"], "(sequence turn_left turn_right)"),
        (["REPEAT", "R=19", "r(", "move", "r)"], "(repeat 19 move)"),
        (["IF", "c(", "leftIsClear", "c)", "i(", "move", "i)"], "(when_karel left_is_clear move)"),
        (
            ["IFELSE", "c(", "rightIsClear", "c)", "i(", "turnRight", "i)", "ELSE", "e(", "pickMarker", "e)"],
            "(if_karel right_is_clear turn_right pick_marker)",
        ),
        (
            ["WHILE", "c(", "not", "c(", "noMarkersPresent", "c)", "c)", "w(", "pickMarker", "w)"],
            "(while_karel 200 (not_karel no_markers_present) pick_marker)",
        ),
    ],
)
def test_all_published_grammar_forms_translate_to_aeon(tokens, expected):
    assert dataset.translate_tokens(["DEF", "run", "m(", *tokens, "m)"]) == expected


@pytest.mark.parametrize(
    "tokens",
    [
        [],
        ["DEF", "run", "m(", "m)"],
        ["DEF", "run", "m(", "move", "m)", "bad"],
        ["DEF", "run", "m(", "REPEAT", "R=-1", "r(", "move", "r)", "m)"],
        ["DEF", "run", "m(", "WHILE", "c(", "bad", "c)", "w(", "move", "w)", "m)"],
    ],
)
def test_bad_programs_are_not_approximated(tokens):
    with pytest.raises(ValueError):
        dataset.translate_tokens(tokens)


def test_published_crash_semantics_and_marker_limit():
    strict = replace(k.world(3, 3, 2, 1, 1), strict=True, marker_limit=101)
    assert k.fitness(k.move, k.example(strict, strict)) == 1
    assert k.fitness(k.pick_marker, k.example(strict, strict)) == 1
    assert k.move(replace(strict, strict=False)) == strict
    stack = k.with_markers(strict, 2, 1, 10)
    assert k.marker_count(k.put_marker(stack)) == 11
    assert k.marker_count(k.pick_marker(k.put_marker(stack))) == 10
    assert k.fitness(k.put_marker, k.example(k.with_markers(strict, 2, 1, 101), strict)) == 1


def test_global_tick_budget_is_shared_and_reset_between_examples():
    strict = replace(k.world(3, 3, 1, 1, 1), strict=True, marker_limit=101)

    def many(w):
        for _ in range(200):
            w = k.turn_right(w)
        return w

    def too_many(w):
        return k.turn_right(many(w))

    assert k.fitness(many, k.example(strict, strict) * 2) == 0
    assert k.fitness(too_many, k.example(strict, strict)) == 1

    # Predicate evaluations and repeat iterations also consume a global tick.
    def many_predicates(w):
        for _ in range(201):
            k.front_is_clear(w)
        return w

    assert k.fitness(many_predicates, k.example(strict, strict)) == 1
    assert k.front_is_clear(strict)  # no leaked budget after failure


def imported_payload(record, mode="validate"):
    pairs = [tuple(dataset.encode_world(w) for w in dataset.decode_example(example)) for example in record["examples"]]
    return {
        "mode": mode,
        "synthesizer": "enumerative",
        "budget": 5,
        "observed": {"id": 0, "guid": record["guid"], "pairs": pairs[:5]},
        "heldout": {"id": 0, "guid": record["guid"], "pairs": pairs[5:]},
        "expression": dataset.translate_tokens(record["program_tokens"]),
    }


def test_translated_reference_executes_in_aeon_on_all_six_examples():
    payload = imported_payload(source_record())
    assert run_task(payload)["generalizes"]


def test_nested_reference_executes_in_aeon():
    tokens = [
        "DEF",
        "run",
        "m(",
        "WHILE",
        "c(",
        "not",
        "c(",
        "noMarkersPresent",
        "c)",
        "c)",
        "w(",
        "pickMarker",
        "w)",
        "REPEAT",
        "R=4",
        "r(",
        "turnLeft",
        "r)",
        "IFELSE",
        "c(",
        "frontIsClear",
        "c)",
        "i(",
        "move",
        "i)",
        "ELSE",
        "e(",
        "turnRight",
        "e)",
        "m)",
    ]

    def reference(w):
        return k.move(k.pick_marker(k.pick_marker(w)))

    payload = imported_payload(source_record(tokens, reference))
    assert run_task(payload)["generalizes"]


def test_aeon_repeat_obeys_global_budget_and_allows_intermediate_marker_stacks():
    record = source_record(
        ["DEF", "run", "m(", "REPEAT", "R=9", "r(", "putMarker", "r)", "REPEAT", "R=9", "r(", "pickMarker", "r)", "m)"],
        lambda w: w,
    )
    assert run_task(imported_payload(record))["generalizes"]
    payload = imported_payload(source_record(program=lambda w: w))
    payload["expression"] = "(repeat 101 turn_right)"
    result = run_task(payload)
    assert result["observed_failures"] == 5 and result["heldout_failures"] == 1


def test_materialized_holes_typecheck_without_labels_or_holdout(tmp_path):
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI

    source = tmp_path / "test.json"
    source.write_text(json.dumps(source_record()) + "\n", encoding="utf-8")
    split = tmp_path / "split"
    dataset.import_split(source, split)
    task = tmp_path / "task"
    dataset.materialize_task(split, 0, task)
    hole = (task / "synth.ae").read_text(encoding="utf-8")
    assert "?hole" in hole and "heldout" not in hole and "reference" not in hole
    assert "program_tokens" not in (task / "observed.json").read_text(encoding="utf-8")
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True))
    assert list(driver.parse(str(task / "synth.ae"))) == [] and driver.has_synth()
    from aeon.core.types import top, t_unit
    from aeon.synthesis.identification import get_holes_info

    holes = get_holes_info(driver.typing_ctx, driver.core, top, driver.incomplete_functions)
    for _, context in holes.values():
        variables = {name.name: ty for name, ty in context.concrete_vars()}
        assert variables["specification"] == t_unit
        assert all(variables[f"Karel_{name}"] == t_unit for name in dataset.HIDDEN_KAREL_NAMES)
    with pytest.raises(FileExistsError):
        dataset.materialize_task(split, 0, task)


def test_actual_synthesis_uses_five_examples_then_evaluates_the_holdout():
    payload = imported_payload(source_record(), "synthesize")
    payload.pop("expression")
    assert run_task(payload)["generalizes"]


def test_holdout_does_not_affect_synthesis_fitness():
    payload = imported_payload(source_record(), "synthesize")
    payload.pop("expression")
    initial = dataset.decode_world(payload["heldout"]["pairs"][0][0])
    payload["heldout"]["pairs"][0] = (dataset.encode_world(initial), dataset.encode_world(k.turn_left(initial)))
    result = run_task(payload)
    assert result["consistent"] and not result["generalizes"]
    assert result["observed_failures"] == 0 and result["heldout_failures"] == 1


def test_isolated_runner_deadline():
    assert run_isolated(imported_payload(source_record()), 0.001)["status"] == "timeout"


def test_cli_import_materialize_and_complete_reference_report(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    for split in ("train", "val", "test"):
        (source / f"{split}.json").write_text(json.dumps(source_record()) + "\n", encoding="utf-8")
    out = tmp_path / "out"
    commands = [
        [sys.executable, "scripts/import_karel_dataset.py", "import", "--source", str(source), "--out", str(out)],
        [
            sys.executable,
            "scripts/import_karel_dataset.py",
            "materialize",
            "--split",
            str(out / "test"),
            "--out",
            str(tmp_path / "tasks"),
        ],
        [
            sys.executable,
            "-m",
            "aeon.benchmarks.karel_runner",
            "--split",
            str(out / "test"),
            "--results",
            str(tmp_path / "results.jsonl"),
        ],
    ]
    for command in commands:
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=60)
        assert result.returncode == 0, result.stdout + result.stderr
    summary = json.loads((tmp_path / "results.jsonl.summary.json").read_text(encoding="utf-8"))
    assert summary["all_references_validated"] and summary["full_split"] and summary["tasks"] == 1
    assert (tmp_path / "tasks/0000000/synth.ae").exists()
    manifest = json.loads((out / "corpus_manifest.json").read_text(encoding="utf-8"))
    assert not manifest["paper_size_matches"] and not manifest["all_references_validated"]
    result = subprocess.run(
        [
            sys.executable,
            "scripts/import_karel_dataset.py",
            "import",
            "--source",
            str(source),
            "--out",
            str(tmp_path / "wrong-size"),
            "--require-paper-size",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode != 0 and "do not match the paper" in result.stderr
