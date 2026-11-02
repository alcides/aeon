"""Translate the ground examples without replacing them with guessed algorithms."""

import json
import random

from .common import Group, example_program, identifier, merge_type, sexprs, value_type


def l2(corpus):
    for path in sorted((corpus.source_root / "l2/benchmarks").glob("*.json")):
        task = json.loads(path.read_text())
        assert task["kind"] == "examples"
        examples = []
        types = []
        for raw in task["contents"]["examples"]:
            call, arrow, output = sexprs(raw)
            assert isinstance(call, Group) and call.bracket == "(" and arrow == "->"
            inputs = call.items[1:]
            row = [value_type(x) for x in [*inputs, output]]
            types = [merge_type(a, b) for a, b in zip(types, row, strict=True)] if types else row
            examples.append((inputs, output))
        prelude = (
            "open Seq\nopen RoseTree\n"
            if "RoseTree" in str(types)
            else "open Seq\nopen Maybe\nopen Pair\nopen Functional\n"
        )
        # The original context is retained in the manifest. Aeon's shared library
        # is deliberately reported as a different, larger synthesis context.
        corpus.add(
            "l2",
            path.stem,
            path,
            example_program(types, examples, prelude),
            specification="examples",
            examples=len(examples),
            original_background=task["contents"].get("background", []),
            original_blacklist=task.get("blacklist", []),
            description=task.get("description", ""),
        )


def dreamcoder(corpus):
    path = corpus.source_root / "dreamcoder/data/list_tasks.json"
    tasks = json.loads(path.read_text())
    mapping = {"int": "Int", "bool": "Bool", "list-of-int": ("Seq", "Int"), "list-of-bool": ("Seq", "Bool")}
    for index, task in enumerate(tasks):
        types = [mapping[task["type"]["input"]], mapping[task["type"]["output"]]]
        examples = [([ex["i"]], ex["o"]) for ex in task["examples"]]
        corpus.add(
            "dreamcoder",
            f"{index:03d}_{identifier(task['name'])}",
            path,
            example_program(types, examples),
            specification="examples",
            examples=len(examples),
            original_name=task["name"],
        )
    # The pinned loader also appends these three training tasks. Its examples
    # are randomized at runtime, so label our deterministic regeneration.
    path = corpus.source_root / "dreamcoder/dreamcoder/domains/list/makeListTasks.py"
    rng = random.Random(639)
    for index, name in enumerate(("sort-and-deduplicate", "+1 maximum list", "range +1 maximum list")):
        examples = []
        for _ in range(15):
            xs = [rng.randint(0, 10) for _ in range(rng.randint(2, 5))]
            if index == 0:
                xs = list(dict.fromkeys(xs))
                output = sorted(xs)
            elif index == 1:
                output = max(xs) + 1
            else:
                output = list(range(max(xs) + 1))
            examples.append(([xs], output))
        types = [("Seq", "Int"), "Int" if index == 1 else ("Seq", "Int")]
        corpus.add(
            "dreamcoder/bootstrap",
            identifier(name),
            path,
            example_program(types, examples),
            specification="regenerated-examples",
            examples=15,
            seed=639,
            original_name=name,
        )
