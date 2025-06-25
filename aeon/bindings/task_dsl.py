import json
import numpy as np
from typing import List, Tuple, Callable
import os

# Type aliases for clarity
Grid = List[List[int]]
Example = Tuple[Grid, Grid]
Task = Tuple[List[Example], List[Example]]  # (train, test)


def load_task_impl(filename: str) -> Task:
    """Load an ARC task from a JSON file."""
    with open(filename, "r") as f:
        data = json.load(f)
    train = []
    test = []
    for example in data.get("train", []):
        input_grid = example["input"]
        output_grid = example["output"]
        train.append((input_grid, output_grid))
    for example in data.get("test", []):
        input_grid = example["input"]
        output_grid = example.get("output", None)
        test.append((input_grid, output_grid))
    return (train, test)


def load_arc_task_by_id(task_id: str) -> Task:
    arc_data_path = os.environ.get("ARC_DATA_PATH", "/Users/paulo/Desktop/ARC-AGI/data/evaluation")
    file_path = os.path.join(arc_data_path, f"{task_id}.json")
    with open(file_path) as f:
        data = json.load(f)
    train = [(ex["input"], ex["output"]) for ex in data["train"]]
    test = [(ex["input"], ex.get("output")) for ex in data["test"]]
    return (train, test)


# --- DSL Primitives ---
def mirror_horizontal(grid: Grid) -> Grid:
    """Mirror the grid along the horizontal axis (top-bottom flip)."""
    return grid[::-1]


def mirror_vertical(grid: Grid) -> Grid:
    """Mirror the grid along the vertical axis (left-right flip)."""
    return [row[::-1] for row in grid]


def rotate_90(grid: Grid) -> Grid:
    """Rotate the grid 90 degrees clockwise."""
    return np.rot90(np.array(grid), k=-1).tolist()


def glue_horizontal(grid1: Grid, grid2: Grid) -> Grid:
    """Glue two grids horizontally (side by side)."""
    assert len(grid1) == len(grid2), "Grids must have the same number of rows to combine horizontally."
    return [row1 + row2 for row1, row2 in zip(grid1, grid2)]


def glue_vertical(grid1: Grid, grid2: Grid) -> Grid:
    """Glue two grids vertically (one on top of the other)."""
    assert len(grid1[0]) == len(grid2[0]), "Grids must have the same number of columns to combine vertically."
    return grid1 + grid2


# --- Evaluation ---
def _evaluate_on_dataset(program: Callable, dataset: List[Tuple[Grid, Grid]]) -> float:
    """
    Evaluate a candidate program on a dataset (list of (input, expected_output) pairs).
    Returns the average percentage of pixels that the program gets right.
    """
    total_score = 0.0
    total_examples = 0
    try:
        for input_grid, expected_output in dataset:
            if expected_output is None:
                continue  # Skip if no ground truth
            actual_output = program(input_grid)
            arr_actual = np.array(actual_output)
            arr_expected = np.array(expected_output)
            if arr_actual.shape != arr_expected.shape:
                # If output shape is wrong, score is 0 for this example
                continue
            total_pixels = arr_expected.size
            correct_pixels = np.sum(arr_actual == arr_expected)
            total_score += correct_pixels / total_pixels
            total_examples += 1
        return total_score / total_examples if total_examples > 0 else 0.0
    except Exception:
        return -1
    
def _evaluate_on_dataset_multi(program: Callable, dataset: List[Tuple[Grid, Grid]]) -> List[float]:
    """
    Evaluates a program on a dataset and returns a LIST of scores, one for each example.
    This is required for Lexicase and Multi-Objective selection.
    """
    scores = []
    for input_grid, expected_output in dataset:
        score = 0.0
        if expected_output is not None:
            try:
                actual_output = np.array(program(input_grid))
                expected_output = np.array(expected_output)
                if actual_output.shape == expected_output.shape:
                    score = np.sum(actual_output == expected_output) / expected_output.size
            except Exception:
                score = -1
        scores.append(score)
    return scores

def evaluate_on_train_impl_multi(program, task):
    train, _ = task
    return _evaluate_on_dataset_multi(program, train)

def evaluate_on_train_impl(program, task):
    train, _ = task
    return _evaluate_on_dataset(program, train)


def evaluate_on_test_impl(program, task):
    _, test = task
    return _evaluate_on_dataset(program, test)
