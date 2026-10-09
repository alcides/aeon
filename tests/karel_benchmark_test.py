"""2D Karel semantics, tensor compatibility, and Aeon benchmark integration."""

from pathlib import Path
import subprocess
import sys

import numpy as np
import pytest

from aeon.bindings import karel as k


ROOT = Path(__file__).resolve().parent.parent
SUITE = ROOT / "examples/synthesis/karel"
CASES = ["move", "turn", "pick", "put", "repeat", "conditional", "while", "harvest", "left", "right"]


@pytest.mark.parametrize("facing,position", [(0, (2, 1)), (1, (3, 2)), (2, (2, 3)), (3, (1, 2))])
def test_movement_and_rotation_in_all_directions(facing, position):
    initial = k.world(5, 5, 2, 2, facing)
    moved = k.move(initial)
    assert (moved.x, moved.y) == position
    assert k.turn_left(k.turn_right(initial)) == initial
    assert k.turn_right(initial).facing == (facing + 1) % 4
    assert k.turn_left(initial).facing == (facing - 1) % 4
    assert (initial.x, initial.y) == (2, 2)


def test_walls_boundaries_and_relative_sensors():
    initial = k.with_wall(k.world(4, 3, 1, 1, 1), 2, 1)
    assert not k.front_is_clear(initial)
    assert k.left_is_clear(initial) and k.right_is_clear(initial)
    assert k.move(initial) == initial
    assert not k.front_is_clear(k.world(4, 3, 0, 0, 0))
    assert not k.left_is_clear(k.world(4, 3, 0, 0, 0))


def test_markers_are_per_cell_immutable_and_bounded():
    initial = k.with_markers(k.world(3, 3, 1, 1, 1), 1, 1, 2)
    initial = k.with_markers(initial, 2, 1, 5)
    assert k.marker_count(k.pick_marker(initial)) == 1
    assert k.marker_count(k.put_marker(initial)) == 3
    assert k.marker_count(k.move(initial)) == 5
    assert k.marker_count(initial) == 2
    empty = k.with_markers(initial, 1, 1, 0)
    assert not k.markers_present(empty)
    assert k.pick_marker(empty) == empty
    with pytest.raises(ValueError, match="10 markers"):
        k.put_marker(k.with_markers(empty, 1, 1, 10))
    # A rendered robot obscures markers; fitness must compare complete states.
    assert k.render(initial) == k.render(empty)
    assert not k.same_world(initial, empty)


@pytest.mark.parametrize("args", [(0, 3, 0, 0, 0), (3, 3, 3, 0, 0), (3, 3, 0, 0, 4)])
def test_invalid_worlds_are_rejected(args):
    with pytest.raises(ValueError):
        k.world(*args)


def test_invalid_wall_and_marker_locations_are_rejected():
    initial = k.world(3, 3, 1, 1, 0)
    with pytest.raises(ValueError):
        k.with_wall(initial, 1, 1)
    with pytest.raises(ValueError):
        k.with_wall(initial, 3, 1)
    with pytest.raises(ValueError):
        k.with_markers(k.with_wall(initial, 2, 2), 2, 2, 1)
    with pytest.raises(ValueError):
        k.with_markers(initial, 2, 2, -1)


@pytest.mark.parametrize("facing,channel", [(0, 0), (1, 3), (2, 1), (3, 2)])
def test_upstream_tensor_encoding(facing, channel):
    initial = k.with_wall(k.world(4, 3, 1, 1, facing), 0, 2)
    initial = k.with_markers(initial, 1, 1, 10)
    tensor = k.to_tensor(initial)
    assert np.asarray(tensor).shape == (3, 4, 16)
    assert tensor[1][1][channel] == 1
    assert tensor[1][1][15] == 1
    assert tensor[2][0][4] == 1
    assert tensor[2][0][5] == 1
    assert k.from_tensor(tensor) == initial


def test_load_upstream_npz_shapes_and_score_candidates(tmp_path):
    initial = k.world(3, 3, 1, 1, 1)
    expected = k.move(initial)
    inputs, outputs = np.asarray([k.to_tensor(initial)]), np.asarray([k.to_tensor(expected)])
    path = tmp_path / "source.npz"
    np.savez(path, inputs=inputs, outputs=outputs, codes=np.array([["irrelevant"]], dtype=object))
    dataset = k.load_examples(str(path))
    assert dataset == (((initial, expected),),)
    assert k.fitness(k.move, dataset[0]) == 0.0
    assert k.fitness(k.turn_left, dataset[0]) == 1.0
    assert k.fitness(lambda _: "invalid", dataset[0]) == 1.0
    np.savez(path, inputs=inputs[:, None], outputs=outputs[:, None])
    assert k.load_examples(str(path)) == dataset


@pytest.mark.parametrize("case", CASES)
def test_embedded_reference_tasks_run_in_aeon(case):
    result = subprocess.run(
        [sys.executable, "-m", "aeon", str(SUITE / "reference" / f"{case}.ae")],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == "0.0", result.stdout + result.stderr


@pytest.mark.parametrize("case", CASES)
def test_embedded_synthesis_tasks_typecheck_with_holes(case):
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI

    driver = AeonDriver(
        AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    )
    assert driver.parse(str(SUITE / "synth" / f"{case}.ae")) == []
    assert driver.has_synth()


def test_exhausted_loop_candidate_is_a_failure():
    initial = k.world(3, 3, 1, 1, 1)

    def exhausted(w):
        return k.require_finished(0, k.front_is_clear, w)

    assert k.fitness(exhausted, k.example(initial, initial)) == 1.0
    assert k.require_finished(0, k.front_is_clear, k.world(3, 3, 2, 1, 1)).x == 2


def test_seeded_worlds_follow_generator_defaults():
    for seed in range(10):
        w = k.random_world(8, 8, seed)
        assert w == k.random_world(8, 8, seed)
        assert (w.x, w.y) not in w.walls
        assert all((x, 0) in w.walls and (x, 7) in w.walls for x in range(8))
        assert all((0, y) in w.walls and (7, y) in w.walls for y in range(8))
        assert all(count == 1 for _, _, count in w.markers)


def test_aeon_synthesizes_a_program_with_zero_fitness():
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "enumerative", "--budget", "5", str(SUITE / "synth/move.ae")],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=40,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert "[0.0]" in result.stdout and "?hole: Karel_move w" in result.stdout


def test_upstream_dataset_is_available_inside_aeon(tmp_path):
    initial = k.with_markers(k.world(4, 3, 1, 1, 1), 2, 1, 2)
    expected = k.move(initial)
    dataset = tmp_path / "source.npz"
    np.savez(dataset, inputs=[k.to_tensor(initial)], outputs=[k.to_tensor(expected)])
    program = tmp_path / "dataset.ae"
    program.write_text(
        "import Karel;\nopen Karel\n"
        f'def data : Dataset := load_dataset "{dataset}"\n'
        "def main (_: Int) : Unit := print (fitness move (dataset_task data 0))\n",
        encoding="utf-8",
    )
    result = subprocess.run(
        [sys.executable, "-m", "aeon", str(program)], cwd=ROOT, capture_output=True, text=True, timeout=30
    )
    assert result.returncode == 0 and result.stdout.strip() == "0.0", result.stdout + result.stderr


def test_nested_aeon_combinators_and_marker_state(tmp_path):
    program = tmp_path / "nested.ae"
    program.write_text(
        "import Karel;\nopen Karel\n"
        "def initial : World := with_markers (world 4 3 1 1 east) 2 1 2\n"
        "def expected : World := world 4 3 2 1 east\n"
        "def collect (w: World) : World := while_karel 19 markers_present pick_marker w\n"
        "def solution (w: World) : World := sequence (when_karel (not_karel no_markers_present) stay) (sequence move collect) w\n"
        "def main (_: Int) : Unit := print (fitness solution (example initial expected))\n",
        encoding="utf-8",
    )
    result = subprocess.run(
        [sys.executable, "-m", "aeon", str(program)], cwd=ROOT, capture_output=True, text=True, timeout=30
    )
    assert result.returncode == 0 and result.stdout.strip() == "0.0", result.stdout + result.stderr
