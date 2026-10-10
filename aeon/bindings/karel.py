"""Immutable two-dimensional worlds for Aeon's embedded Karel combinators.

Coordinates start at the top left; directions are north/east/south/west (0–3).
Blocked moves and empty picks leave the world unchanged, as in carpedm20/karel.
"""

from contextvars import ContextVar
from dataclasses import dataclass, field, replace
import random


DELTAS = ((0, -1), (1, 0), (0, 1), (-1, 0))


@dataclass
class ExecutionBudget:
    limit: int = 200
    ticks: int = 0


_budget: ContextVar[ExecutionBudget | None] = ContextVar("karel_execution_budget", default=None)


def tick() -> None:
    budget = _budget.get()
    if budget is not None:
        if budget.ticks >= budget.limit:
            raise RuntimeError("Karel program exhausted its global tick budget")
        budget.ticks += 1


def repeat_tick(w: "World") -> "World":
    tick()
    return w


@dataclass(frozen=True)
class World:
    width: int
    height: int
    x: int
    y: int
    facing: int
    walls: frozenset[tuple[int, int]] = frozenset()
    markers: tuple[tuple[int, int, int], ...] = ()
    # Policy is not part of physical world equality. The published MSR artifact
    # crashes on invalid actions and permits intermediate stacks through 101.
    strict: bool = field(default=False, compare=False)
    marker_limit: int = field(default=10, compare=False)

    def __post_init__(self):
        if self.width < 1 or self.height < 1:
            raise ValueError("world dimensions must be positive")
        if self.facing not in range(4):
            raise ValueError("direction must be 0 (north), 1 (east), 2 (south), or 3 (west)")
        if not self.inside(self.x, self.y) or (self.x, self.y) in self.walls:
            raise ValueError("robot must occupy a clear cell inside the world")
        if any(not self.inside(x, y) for x, y in self.walls):
            raise ValueError("walls must be inside the world")
        for x, y, count in self.markers:
            if not self.inside(x, y) or (x, y) in self.walls or not 1 <= count <= self.marker_limit:
                raise ValueError("markers require a clear cell and a count within the world's marker limit")

    def inside(self, x: int, y: int) -> bool:
        return 0 <= x < self.width and 0 <= y < self.height


def world(width: int, height: int, x: int, y: int, facing: int) -> World:
    return World(width, height, x, y, facing)


def random_world(width: int, height: int, seed: int) -> World:
    """Source generator defaults: border walls, 0.1 wall/marker probability.

    Aeon uses its own deterministic RNG; seeds are not NumPy seed equivalents.
    """
    if width <= 2 or height <= 2:
        raise ValueError("random worlds need an interior (width and height > 2)")
    rng = random.Random(seed)
    walls = {
        (x, y)
        for y in range(height)
        for x in range(width)
        if x in (0, width - 1) or y in (0, height - 1) or rng.random() < 0.1
    }
    x, y, facing = rng.randrange(1, width - 1), rng.randrange(1, height - 1), rng.randrange(4)
    walls.discard((x, y))
    markers = tuple(
        (px, py, 1)
        for py in range(1, height - 1)
        for px in range(1, width - 1)
        if (px, py) not in walls and rng.random() < 0.1
    )
    return World(width, height, x, y, facing, frozenset(walls), tuple(sorted(markers)))


def with_wall(w: World, x: int, y: int) -> World:
    return replace(w, walls=w.walls | {(x, y)})


def with_markers(w: World, x: int, y: int, count: int) -> World:
    if not w.inside(x, y) or (x, y) in w.walls or not 0 <= count <= w.marker_limit:
        raise ValueError("invalid marker cell or count")
    counts = {(px, py): n for px, py, n in w.markers}
    if count:
        counts[x, y] = count
    else:
        counts.pop((x, y), None)
    return replace(w, markers=tuple((px, py, n) for (px, py), n in sorted(counts.items())))


def marker_count_at(w: World, x: int, y: int) -> int:
    if not w.inside(x, y):
        raise ValueError("cell outside world")
    return next((n for px, py, n in w.markers if (px, py) == (x, y)), 0)


def marker_count(w: World) -> int:
    return marker_count_at(w, w.x, w.y)


def clear(w: World, facing: int) -> bool:
    dx, dy = DELTAS[facing]
    x, y = w.x + dx, w.y + dy
    return w.inside(x, y) and (x, y) not in w.walls


def front_is_clear(w: World) -> bool:
    tick()
    return clear(w, w.facing)


def left_is_clear(w: World) -> bool:
    tick()
    return clear(w, (w.facing - 1) % 4)


def right_is_clear(w: World) -> bool:
    tick()
    return clear(w, (w.facing + 1) % 4)


def markers_present(w: World) -> bool:
    tick()
    return marker_count(w) > 0


def move(w: World) -> World:
    tick()
    dx, dy = DELTAS[w.facing]
    if clear(w, w.facing):
        return replace(w, x=w.x + dx, y=w.y + dy)
    if w.strict:
        raise RuntimeError("Karel crashed: blocked move")
    return w


def turn_left(w: World) -> World:
    tick()
    return replace(w, facing=(w.facing - 1) % 4)


def turn_right(w: World) -> World:
    tick()
    return replace(w, facing=(w.facing + 1) % 4)


def pick_marker(w: World) -> World:
    tick()
    if marker_count(w):
        return with_markers(w, w.x, w.y, marker_count(w) - 1)
    if w.strict:
        raise RuntimeError("Karel crashed: empty marker pick")
    return w


def put_marker(w: World) -> World:
    tick()
    count = marker_count(w)
    if count >= w.marker_limit:
        raise ValueError(f"Karel world supports at most {w.marker_limit} markers per cell")
    return with_markers(w, w.x, w.y, count + 1)


def render(w: World) -> str:
    """Display the world (robot glyph hides markers beneath the robot)."""
    grid = [["." for _ in range(w.width)] for _ in range(w.height)]
    for x, y in w.walls:
        grid[y][x] = "#"
    for x, y, count in w.markers:
        grid[y][x] = str(count) if count < 10 else "A"
    grid[w.y][w.x] = "^>v<"[w.facing]
    return "\n".join("".join(row) for row in grid)


def same_world(left: World, right: World) -> bool:
    return left == right


def require_finished(fuel: int, test, w: World) -> World:
    if fuel <= 0 and test(w):
        raise RuntimeError("Karel loop exhausted its execution budget")
    return w


def to_tensor(w: World) -> list[list[list[int]]]:
    """carpedm20 H × W × 16 encoding, with N/S/W/E direction channels."""
    tensor = [[[0] * 16 for _ in range(w.width)] for _ in range(w.height)]
    for y in range(w.height):
        for x in range(w.width):
            tensor[y][x][4] = int((x, y) in w.walls)
            count = marker_count_at(w, x, y)
            if count > 10:
                raise ValueError("Karel tensor format supports at most 10 markers per cell")
            tensor[y][x][5 + count] = 1
    tensor[w.y][w.x][(0, 3, 1, 2)[w.facing]] = 1
    return tensor


def from_tensor(tensor) -> World:
    height = len(tensor)
    width = len(tensor[0]) if height else 0
    if not width or any(len(row) != width for row in tensor):
        raise ValueError("tensor must be a non-empty rectangle")
    walls, markers, robots = set(), [], []
    for y, row in enumerate(tensor):
        for x, cell in enumerate(row):
            if len(cell) != 16 or any(value not in (0, 1) for value in cell) or sum(cell[5:]) != 1:
                raise ValueError("invalid Karel tensor cell")
            if cell[4]:
                walls.add((x, y))
            count = next(i for i, value in enumerate(cell[5:]) if value)
            if count:
                markers.append((x, y, count))
            for channel, value in enumerate(cell[:4]):
                if value:
                    robots.append((x, y, (0, 2, 3, 1)[channel]))
    if len(robots) != 1:
        raise ValueError("tensor must contain exactly one robot")
    x, y, facing = robots[0]
    return World(width, height, x, y, facing, frozenset(walls), tuple(sorted(markers)))


def load_examples(path: str):
    """Load upstream generator .npz inputs/outputs, without executing stored code.

    The source generator uses N × H × W × 16 arrays (one I/O per program).
    Also accept N × E × H × W × 16 datasets with multiple examples per task.
    """
    if not path.endswith(".npz"):
        from aeon.benchmarks.karel import JsonlDataset

        return JsonlDataset(path)

    import numpy as np

    with np.load(path, allow_pickle=False) as dataset:
        inputs, outputs = dataset["inputs"], dataset["outputs"]
        if inputs.shape != outputs.shape or inputs.ndim not in (4, 5) or inputs.shape[-1] != 16:
            raise ValueError("Karel inputs/outputs must have matching N [× E] × H × W × 16 shapes")
        if inputs.ndim == 4:
            return tuple(((from_tensor(a), from_tensor(b)),) for a, b in zip(inputs, outputs))
        return tuple(tuple((from_tensor(a), from_tensor(b)) for a, b in zip(xs, ys)) for xs, ys in zip(inputs, outputs))


def fitness(program, examples) -> float:
    """Count failed whole-world examples, including crashes and loop exhaustion."""
    failures = 0
    for initial, expected in examples:
        token = _budget.set(ExecutionBudget() if initial.strict else None)
        try:
            actual = program(initial)
            failures += int(not isinstance(actual, World) or not same_world(actual, expected))
        except (RuntimeError, ValueError, TypeError, RecursionError):
            failures += 1
        finally:
            _budget.reset(token)
    return float(failures)


def example(initial: World, expected: World):
    return ((initial, expected),)


def append_examples(left, right):
    return left + right
