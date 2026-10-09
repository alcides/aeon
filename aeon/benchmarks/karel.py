"""A dependency-free interpreter for the Karel synthesis benchmark DSL.

Compatible with the token syntax used by carpedm20/karel.  Worlds are immutable
ASCII grids, making generated input/output examples deterministic and portable.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import random


class Direction(str, Enum):
    NORTH = "^"
    SOUTH = "v"
    WEST = "<"
    EAST = ">"

    def right(self) -> "Direction":
        return {self.NORTH: self.EAST, self.EAST: self.SOUTH, self.SOUTH: self.WEST, self.WEST: self.NORTH}[self]

    def left(self) -> "Direction":
        return {self.NORTH: self.WEST, self.WEST: self.SOUTH, self.SOUTH: self.EAST, self.EAST: self.NORTH}[self]

    @property
    def delta(self) -> tuple[int, int]:
        return {self.NORTH: (0, -1), self.SOUTH: (0, 1), self.WEST: (-1, 0), self.EAST: (1, 0)}[self]


@dataclass(frozen=True)
class World:
    rows: tuple[str, ...]
    x: int
    y: int
    direction: Direction
    markers: tuple[tuple[int, int, int], ...] = ()

    @classmethod
    def parse(cls, text: str) -> "World":
        rows = tuple(line.strip() for line in text.strip().splitlines())
        if not rows or len({len(row) for row in rows}) != 1:
            raise ValueError("world must be a non-empty rectangle")
        hero = [(x, y, Direction(char)) for y, row in enumerate(rows) for x, char in enumerate(row) if char in "^v<>"]
        if len(hero) != 1:
            raise ValueError("world needs exactly one robot")
        x, y, direction = hero[0]
        markers = tuple((x, y, int(char)) for y, row in enumerate(rows) for x, char in enumerate(row) if char.isdigit())
        clean = tuple("".join("." if char in "^v<>" or char.isdigit() else char for char in row) for row in rows)
        return cls(clean, x, y, direction, markers)

    def render(self) -> str:
        grid = [list(row) for row in self.rows]
        for x, y, count in self.markers:
            grid[y][x] = str(count)
        grid[self.y][self.x] = self.direction.value
        return "\n".join("".join(row) for row in grid)

    def marker_count(self, x: int | None = None, y: int | None = None) -> int:
        x, y = self.x if x is None else x, self.y if y is None else y
        return next((count for px, py, count in self.markers if (px, py) == (x, y)), 0)

    def clear(self, direction: Direction) -> bool:
        dx, dy = direction.delta
        nx, ny = self.x + dx, self.y + dy
        return 0 <= ny < len(self.rows) and 0 <= nx < len(self.rows[0]) and self.rows[ny][nx] != "#"

    def update_markers(self, count: int) -> "World":
        markers = {(x, y): n for x, y, n in self.markers}
        if count:
            markers[self.x, self.y] = count
        else:
            markers.pop((self.x, self.y), None)
        return World(
            self.rows, self.x, self.y, self.direction, tuple((x, y, n) for (x, y), n in sorted(markers.items()))
        )


Node = tuple


def parse(program: str) -> Node:
    # The source benchmark deliberately treats ``m(``, ``c)``, etc. as tokens.
    tokens = program.split()
    position = 0

    def take(expected: str | None = None) -> str:
        nonlocal position
        if position == len(tokens):
            raise ValueError("unexpected end of Karel program")
        token = tokens[position]
        position += 1
        if expected is not None and token != expected:
            raise ValueError(f"expected {expected!r}, got {token!r}")
        return token

    def block(opening: str, closing: str) -> Node:
        take(opening)
        body = statements(closing)
        take(closing)
        return body

    def statements(closing: str) -> Node:
        nodes = []
        while position < len(tokens) and tokens[position] != closing:
            nodes.append(statement())
        return ("seq", *nodes)

    def condition() -> Node:
        take("c(")
        token = take()
        if token == "not":
            value = condition()
        elif token in {"frontIsClear", "leftIsClear", "rightIsClear", "markersPresent", "noMarkersPresent"}:
            value = ("condition", token)
        else:
            raise ValueError(f"unknown Karel condition {token!r}")
        take("c)")
        return ("not", value) if token == "not" else value

    def statement() -> Node:
        token = take()
        if token in {"move", "turnRight", "turnLeft", "pickMarker", "putMarker"}:
            return ("action", token)
        if token == "REPEAT":
            count = take()
            if not count.startswith("R=") or not count[2:].isdigit():
                raise ValueError("repeat requires R=<non-negative integer>")
            return ("repeat", int(count[2:]), block("r(", "r)"))
        if token == "WHILE":
            return ("while", condition(), block("w(", "w)"))
        if token == "IF":
            return ("if", condition(), block("i(", "i)"))
        if token == "IFELSE":
            cond, yes = condition(), block("i(", "i)")
            take("ELSE")
            return ("ifelse", cond, yes, block("e(", "e)"))
        raise ValueError(f"unknown Karel statement {token!r}")

    take("DEF")
    take("run")
    result = block("m(", "m)")
    if position != len(tokens):
        raise ValueError("trailing Karel input")
    return result


def run(program: str | Node, world: World, step_limit: int = 100) -> World:
    node = parse(program) if isinstance(program, str) else program
    steps = 0

    def condition(test: Node, state: World) -> bool:
        if test[0] == "not":
            return not condition(test[1], state)
        name = test[1]
        if name == "frontIsClear":
            return state.clear(state.direction)
        if name == "leftIsClear":
            return state.clear(state.direction.left())
        if name == "rightIsClear":
            return state.clear(state.direction.right())
        if name == "markersPresent":
            return state.marker_count() > 0
        return state.marker_count() == 0

    def execute(item: Node, state: World) -> World:
        nonlocal steps
        steps += 1
        if steps > step_limit:
            raise RuntimeError("Karel step limit exceeded")
        tag = item[0]
        if tag == "seq":
            for child in item[1:]:
                state = execute(child, state)
            return state
        if tag == "action":
            action = item[1]
            if action == "move" and state.clear(state.direction):
                dx, dy = state.direction.delta
                return World(state.rows, state.x + dx, state.y + dy, state.direction, state.markers)
            if action == "turnRight":
                return World(state.rows, state.x, state.y, state.direction.right(), state.markers)
            if action == "turnLeft":
                return World(state.rows, state.x, state.y, state.direction.left(), state.markers)
            if action == "pickMarker" and state.marker_count():
                return state.update_markers(state.marker_count() - 1)
            if action == "putMarker":
                return state.update_markers(state.marker_count() + 1)
            return state
        if tag == "repeat":
            for _ in range(item[1]):
                state = execute(item[2], state)
            return state
        if tag == "while":
            while condition(item[1], state):
                state = execute(item[2], state)
            return state
        if tag == "if":
            return execute(item[2], state) if condition(item[1], state) else state
        return execute(item[2], state) if condition(item[1], state) else execute(item[3], state)

    return execute(node, world)


def generate_examples(program: str, seed: int = 0, count: int = 2, size: int = 8) -> list[tuple[World, World]]:
    rng, examples = random.Random(seed), []
    for _ in range(count):
        rows = [["#" if x in {0, size - 1} or y in {0, size - 1} else "." for x in range(size)] for y in range(size)]
        x, y = rng.randrange(1, size - 1), rng.randrange(1, size - 1)
        world = World(tuple("".join(row) for row in rows), x, y, rng.choice(list(Direction)))
        examples.append((world, run(program, world)))
    return examples
