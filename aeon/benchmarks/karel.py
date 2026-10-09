"""Import the published MSR Karel corpus into Aeon's embedded DSL.

This is a data adapter and source translator, not a Karel interpreter. Imported
references execute as ordinary Aeon functions using the Karel standard library.
JSONL splits are disk-backed; no generated substitute corpus is called published.
"""

from array import array
from dataclasses import asdict
import gzip
import hashlib
import json
from pathlib import Path
import tempfile
import urllib.request
import zipfile

from aeon.bindings.karel import World


DATASET_PAGE = "https://msr-redmond.github.io/karel-dataset/"
PAPER = "https://arxiv.org/abs/1805.04276"
VALIDATION_URL = (
    "https://huggingface.co/datasets/akdo00001/dataset_Karel/resolve/86ec5251bf3956d598c6e34c4b1b996de3d9e8d8/val.zip"
)
VALIDATION_ARCHIVE_SHA256 = "967dc1c557595e7c4a5ff08a636ec3fe2b5a5320fd6548be50295cf36c5ab4cd"
VALIDATION_JSONL_SHA256 = "612d8564801c80bd39d80fca306e18d76f1694d3fe98cc58215ac96452728b63"
ACTION_NAMES = {
    "move": "move",
    "turnLeft": "turn_left",
    "turnRight": "turn_right",
    "pickMarker": "pick_marker",
    "putMarker": "put_marker",
}
PREDICATE_NAMES = {
    "frontIsClear": "front_is_clear",
    "leftIsClear": "left_is_clear",
    "rightIsClear": "right_is_clear",
    "markersPresent": "markers_present",
    "noMarkersPresent": "no_markers_present",
}
DSL_IMPORT = (
    "import Karel (World, Examples, move, turn_left, turn_right, pick_marker, put_marker, "
    "front_is_clear, left_is_clear, right_is_clear, markers_present, no_markers_present, "
    "not_karel, sequence, repeat, if_karel, when_karel, while_karel, fitness, load_task_examples);\n"
)
# Linked modules retain qualified bindings in the synthesis context even with
# selective imports. Shadow every non-DSL helper by its canonical core name.
HIDDEN_KAREL_NAMES = (
    "north",
    "east",
    "south",
    "west",
    "world",
    "with_wall",
    "random_world",
    "with_markers",
    "marker_count_at",
    "marker_count",
    "render",
    "same_world",
    "example",
    "append_examples",
    "load_dataset",
    "dataset_size",
    "dataset_task",
    "fitness",
    "require_finished",
    "repeat_tick",
    "load_task_examples",
    "robot_x",
    "robot_y",
    "direction",
    "width",
    "height",
    "stay",
)


def fetch_validation(destination: Path) -> dict:
    """Acquire the surviving validation mirror, pinned by revision and two hashes.

    This is only the 2,500-task validation split, not the million-task corpus.
    Extract exactly one known member; never execute or broadly unpack an archive.
    """
    destination.mkdir(parents=True, exist_ok=False)
    with tempfile.TemporaryDirectory(prefix="karel-download-", dir=destination) as directory:
        archive_path = Path(directory) / "val.zip"
        digest = hashlib.sha256()
        with urllib.request.urlopen(VALIDATION_URL, timeout=60) as response, archive_path.open("wb") as stream:
            while chunk := response.read(1024 * 1024):
                digest.update(chunk)
                stream.write(chunk)
        if digest.hexdigest() != VALIDATION_ARCHIVE_SHA256:
            raise ValueError("validation archive SHA-256 mismatch")
        with zipfile.ZipFile(archive_path) as archive:
            if archive.namelist() != ["val.json"]:
                raise ValueError("unexpected validation archive members")
            data = archive.read("val.json")
        if hashlib.sha256(data).hexdigest() != VALIDATION_JSONL_SHA256:
            raise ValueError("validation JSONL SHA-256 mismatch")
        (destination / "val.json").write_bytes(data)
    provenance = {
        "url": VALIDATION_URL,
        "archive_sha256": VALIDATION_ARCHIVE_SHA256,
        "jsonl_sha256": VALIDATION_JSONL_SHA256,
        "split": "val",
        "full_corpus": False,
        "missing_splits": ["train", "test"],
    }
    (destination / "acquisition.json").write_text(json.dumps(provenance, indent=2) + "\n", encoding="utf-8")
    return provenance


def from_grid_json(grid: dict) -> World:
    """MSR coordinates have row zero at the bottom; Aeon y zero is the top."""
    if grid.get("crashed", False):
        raise ValueError("published examples must not contain crashed worlds")
    height, width = int(grid["rows"]), int(grid["cols"])
    if "hero" in grid:
        row, col, direction = grid["hero"].split(":")
        walls = {(int(c), height - 1 - int(r)) for r, c in (v.split(":") for v in grid["blocked"].split())}
        markers = tuple(
            sorted((int(c), height - 1 - int(r), int(n)) for r, c, n in (v.split(":") for v in grid["markers"].split()))
        )
    else:
        row, col, direction = grid["heroRow"], grid["heroCol"], grid["heroDir"]
        walls = {(c, r) for r, line in enumerate(grid["blocked"]) for c, value in enumerate(line) if value == "*"}
        markers = tuple(sorted((int(m["c"]), height - 1 - int(m["r"]), int(m["num"])) for m in grid["markers"]))
    return World(
        width,
        height,
        int(col),
        height - 1 - int(row),
        ("north", "east", "south", "west").index(direction),
        frozenset(walls),
        markers,
        strict=True,
        marker_limit=101,
    )


def from_sparse_tensor(description: str, padding: int = 18) -> World:
    """Decode MSR's flattened C×18×18 sparse tensor, not carpedm20's H×W×C.

    Direction channels are N/E/S/W. Channel 5 outlines the rectangular padding
    boundary, and channels 6–15 encode positive marker counts. Rows are bottom-up.
    """
    active = set()
    for item in description.split():
        index_text, value = item.split(":")
        index = int(index_text)
        if float(value) != 1.0 or not 0 <= index < 16 * padding * padding or index in active:
            raise ValueError("invalid sparse Karel tensor index/value")
        active.add(index)

    def has(channel, row, col):
        return channel * padding * padding + row * padding + col in active

    rows = 0
    while rows < padding and has(5, rows, 0):
        rows += 1
    cols = 0
    while cols < padding and has(5, 0, cols):
        cols += 1
    height, width = rows - 2, cols - 2
    if height < 1 or width < 1:
        raise ValueError("missing rectangular padding boundary")
    boundary = {(r, c) for r in range(rows) for c in range(cols) if r in (0, rows - 1) or c in (0, cols - 1)}
    walls, markers, robots = set(), [], []
    for index in active:
        channel, remainder = divmod(index, padding * padding)
        row, col = divmod(remainder, padding)
        if channel == 5:
            if (row, col) not in boundary:
                raise ValueError("invalid padding channel")
            continue
        if not 1 <= row <= height or not 1 <= col <= width:
            raise ValueError("tensor content outside the world")
        x, y = col - 1, height - row
        if channel < 4:
            robots.append((x, y, channel))
        elif channel == 4:
            walls.add((x, y))
        else:
            markers.append((x, y, channel - 5))
    if any(not has(5, r, c) for r, c in boundary) or len(robots) != 1:
        raise ValueError("tensor requires a complete boundary and exactly one robot")
    if len({(x, y) for x, y, _ in markers}) != len(markers):
        raise ValueError("multiple marker counts in one cell")
    x, y, direction = robots[0]
    return World(
        width, height, x, y, direction, frozenset(walls), tuple(sorted(markers)), strict=True, marker_limit=101
    )


def decode_example(example: dict) -> tuple[World, World]:
    result = []
    for prefix in ("inpgrid", "outgrid"):
        grid = example.get(f"{prefix}_json")
        tensor = example.get(f"{prefix}_tensor")
        if grid is None and tensor is None:
            raise ValueError(f"missing {prefix} world")
        world = from_grid_json(grid) if grid is not None else from_sparse_tensor(tensor)
        if grid is not None and tensor is not None and world != from_sparse_tensor(tensor):
            raise ValueError(f"{prefix} JSON and tensor representations disagree")
        result.append(world)
    if (result[0].width, result[0].height, result[0].walls) != (result[1].width, result[1].height, result[1].walls):
        raise ValueError("Karel actions cannot change dimensions or walls")
    return result[0], result[1]


def encode_world(world: World) -> dict:
    data = asdict(world)
    data["walls"] = sorted(world.walls)
    return data


def decode_world(data: dict) -> World:
    return World(
        **{
            **data,
            "walls": frozenset(tuple(cell) for cell in data["walls"]),
            "markers": tuple(tuple(cell) for cell in data["markers"]),
        }
    )


class JsonlDataset:
    """Random access to original or converted JSONL without retaining worlds.

    An eight-byte offset per task is kept in RAM (8 MB for a million tasks).
    Each access opens its own handle, so no shared seek position or open-file leak.
    """

    def __init__(self, path: str):
        self.path = Path(path)
        self.offsets = array("Q")
        with self.path.open("rb") as stream:
            while True:
                offset = stream.tell()
                line = stream.readline()
                if not line:
                    break
                if line.strip():
                    self.offsets.append(offset)

    def __len__(self):
        return len(self.offsets)

    def record(self, index: int) -> dict:
        if not 0 <= index < len(self):
            raise IndexError("Karel task index out of range")
        with self.path.open("rb") as stream:
            stream.seek(self.offsets[index])
            return json.loads(stream.readline())

    def __getitem__(self, index: int):
        record = self.record(index)
        if "pairs" in record:
            return tuple((decode_world(a), decode_world(b)) for a, b in record["pairs"])
        return tuple(decode_example(example) for example in record["examples"])


def load_task_examples(path: str):
    with open(path, encoding="utf-8") as stream:
        record = json.load(stream)
    return tuple((decode_world(a), decode_world(b)) for a, b in record["pairs"])


def translate_tokens(tokens: list[str]) -> str:
    """Transcode the artifact's serialized tokens into Aeon combinator source.

    No tokens are evaluated in Python. All branches, including unobserved ones,
    are retained. Unknown or truncated syntax fails rather than being approximated.
    """
    position = 0

    def take(expected=None):
        nonlocal position
        if position >= len(tokens):
            raise ValueError("truncated Karel program")
        token = tokens[position]
        position += 1
        if expected is not None and token != expected:
            raise ValueError(f"expected {expected}, got {token}")
        return token

    def condition():
        take("c(")
        token = take()
        if token == "not":
            result = f"(not_karel {condition()})"
        elif token in PREDICATE_NAMES:
            result = PREDICATE_NAMES[token]
        else:
            raise ValueError(f"unknown Karel predicate {token}")
        take("c)")
        return result

    def block(end):
        statements = []
        while position < len(tokens) and tokens[position] != end:
            token = take()
            if token in ACTION_NAMES:
                expression = ACTION_NAMES[token]
            elif token == "REPEAT":
                count = take()
                if not count.startswith("R=") or not count[2:].isdigit():
                    raise ValueError("invalid repeat constant")
                take("r(")
                expression = f"(repeat {int(count[2:])} {block('r)')})"
            elif token in ("IF", "IFELSE", "WHILE"):
                predicate = condition()
                delimiter = "w" if token == "WHILE" else "i"
                take(f"{delimiter}(")
                body = block(f"{delimiter})")
                if token == "IFELSE":
                    take("ELSE")
                    take("e(")
                    alternative = block("e)")
                    expression = f"(if_karel {predicate} {body} {alternative})"
                elif token == "IF":
                    expression = f"(when_karel {predicate} {body})"
                else:
                    expression = f"(while_karel 200 {predicate} {body})"
            else:
                raise ValueError(f"unknown Karel statement {token}")
            statements.append(expression)
        take(end)
        if not statements:
            raise ValueError("empty Karel block")
        expression = statements[-1]
        for statement in reversed(statements[:-1]):
            expression = f"(sequence {statement} {expression})"
        return expression

    take("DEF")
    take("run")
    take("m(")
    expression = block("m)")
    if position < len(tokens) and tokens[position] == "</s>":
        take("</s>")
    if position != len(tokens):
        raise ValueError("trailing Karel tokens")
    return expression


def task_source(examples_path: Path, expression: str | None = None) -> str:
    """A hole gets only the specification examples, never a reference/holdout."""
    path_literal = json.dumps(str(examples_path.resolve()))
    if expression is None:
        shadows = "".join(f"let Karel_{name} := unit in " for name in HIDDEN_KAREL_NAMES)
        declaration = (
            "@minimize(fitness solve specification)\n"
            f"def solve (w: World) : World := let specification := unit in {shadows}?hole\n"
        )
    else:
        declaration = f"def solve (w: World) : World := {expression} w\n"
    return (
        DSL_IMPORT + f"def specification : Examples := load_task_examples {path_literal}\n"
        f"{declaration}"
        "def main (_: Int) : Unit := print (fitness solve specification)\n"
    )


def import_split(source: Path, destination: Path, observed: int = 5, expected_examples: int = 6) -> dict:
    """Stream every source record, with no limit or silent filtering.

    Solutions and held-out worlds are stored separately from specification data.
    Existing destinations are never overwritten. Failure leaves no valid manifest.
    """
    if not 0 < observed < expected_examples:
        raise ValueError("observed count must leave at least one held-out example")
    destination.mkdir(parents=True, exist_ok=False)
    opener = gzip.open if source.suffix == ".gz" else open
    count = 0
    digest = hashlib.sha256()
    with (
        opener(source, "rb") as stream,
        (destination / "observed.jsonl").open("w", encoding="utf-8") as specification,
        (destination / "heldout.jsonl").open("w", encoding="utf-8") as heldout,
        (destination / "references.jsonl").open("w", encoding="utf-8") as references,
    ):
        for line_number, line in enumerate(stream, 1):
            digest.update(line)
            if not line.strip():
                continue
            try:
                record = json.loads(line)
                if len(record["examples"]) != expected_examples:
                    raise ValueError(f"expected {expected_examples} I/O examples")
                pairs = [
                    tuple(encode_world(world) for world in decode_example(example)) for example in record["examples"]
                ]
                expression = translate_tokens(record["program_tokens"])
            except (ValueError, KeyError, TypeError) as error:
                raise ValueError(f"{source}:{line_number}: {error}") from error
            identity = {"id": count, "guid": record.get("guid", str(count))}
            specification.write(json.dumps({**identity, "pairs": pairs[:observed]}) + "\n")
            heldout.write(json.dumps({**identity, "pairs": pairs[observed:]}) + "\n")
            references.write(
                json.dumps(
                    {
                        **identity,
                        "expression": expression,
                        "program_tokens": record["program_tokens"],
                        "program_json": record.get("program_json"),
                        "examples_metadata": [
                            {
                                key: value
                                for key, value in example.items()
                                if key not in ("inpgrid_json", "outgrid_json", "inpgrid_tensor", "outgrid_tensor")
                            }
                            for example in record["examples"]
                        ],
                    }
                )
                + "\n"
            )
            count += 1
    if not count:
        raise ValueError("empty Karel split")
    manifest = {
        "source": str(source.resolve()),
        "source_jsonl_sha256": digest.hexdigest(),
        "tasks": count,
        "observed_examples": observed,
        "heldout_examples": expected_examples - observed,
        "dataset_page": DATASET_PAGE,
        "paper": PAPER,
        "tick_budget": 200,
        "status": "imported-not-yet-reference-validated",
    }
    (destination / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return manifest


def materialize_task(split: Path, index: int, destination: Path) -> None:
    """Emit executable `.ae` reference and hole files for any imported task."""
    materialize_from_datasets(
        JsonlDataset(str(split / "observed.jsonl")),
        JsonlDataset(str(split / "heldout.jsonl")),
        JsonlDataset(str(split / "references.jsonl")),
        index,
        destination,
    )


def materialize_from_datasets(
    observed: JsonlDataset, heldout: JsonlDataset, references: JsonlDataset, index: int, destination: Path
) -> None:
    destination.mkdir(parents=True, exist_ok=False)
    example_path = destination / "observed.json"
    example_path.write_text(json.dumps(observed.record(index)) + "\n", encoding="utf-8")
    (destination / "heldout.json").write_text(json.dumps(heldout.record(index)) + "\n", encoding="utf-8")
    (destination / "reference.ae").write_text(
        task_source(example_path, references.record(index)["expression"]), encoding="utf-8"
    )
    (destination / "synth.ae").write_text(task_source(example_path), encoding="utf-8")
    # Evaluation is run only after synthesis, with the candidate substituted for
    # the reference by the runner; neither candidate context nor fitness reads it.
    (destination / "evaluation.ae").write_text(
        task_source(destination / "heldout.json", references.record(index)["expression"]), encoding="utf-8"
    )
