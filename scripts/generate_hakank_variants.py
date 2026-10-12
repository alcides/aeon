"""Port alternate solver encodings through shared mathematical specifications."""

from copy import deepcopy
import json
from math import isqrt
from pathlib import Path

from scripts.generate_hakank_examples import Model, models as core_models
from scripts.generate_hakank_manual import models as manual_models


ROOT = Path(__file__).resolve().parents[1] / "examples/synthesis/hakank"


def models():
    core = {m.name: m for m in core_models()}
    manual = {m.name: m for m in manual_models()}
    result = []
    equivalents = [
        ("nqueens2", core["nqueens"], "google_or_tools/nqueens2.py"),
        ("mapcoloring2", core["map_coloring"], "oscar/MapColoring2.scala"),
        ("magicsquare2", core["magic_square"], "z3/magic_square2.py"),
        ("magicsquaremip", core["magic_square"], "google_or_tools/magic_square_mip_sat.py"),
        (
            "sendmoremoneyscalarproduct",
            core["send_more_money"],
            "google_or_tools/send_more_money_scalar_product_sat.py",
        ),
        ("donaldgerald", manual["donaldgeraldrobert"], "picat/donald_gerald.pi"),
    ]
    for name, base, source in equivalents:
        model = deepcopy(base)
        model.name = name
        model.source_path = source
        model.generator = "scripts/generate_hakank_variants.py"
        model.data["specification_of"] = base.name
        result.append(model)

    m = deepcopy(core["nqueens"])
    m.name = "queens"
    m.variables = {name: [1, 8] for name in m.variables}
    m.instance = "eight queens, one-based rows as in the Picat source"
    m.source_path = "picat/queens.pi"
    m.generator = "scripts/generate_hakank_variants.py"
    m.data["specification_of"] = "nqueens"
    result.append(m)

    m = Model("alldifferentexcept0test", "six nondecreasing values in 0..6, full source instance")
    values = m.vector("x", 6, 0, 6)
    sequence = m.sequence(values)
    m.constraints = [f"Vec.increasing ({sequence})", f"Vec.allDifferentExceptZero ({sequence})"]
    m.source_path = "jsr_331/AllDifferentExcept0_test.java"
    m.generator = "scripts/generate_hakank_variants.py"
    m.goal = "Synthesize a nondecreasing sequence whose nonzero values are all distinct."
    m.data = dict(length=6)
    result.append(m)

    grids = {
        "sudoku4x4": ("google_or_tools/sudoku_4x4.cs", [[4, 0, 0, 0], [3, 1, 0, 0], [0, 0, 4, 1], [0, 0, 0, 2]]),
        "sudokumip": (
            "google_or_tools/sudoku_mip_sat.py",
            [
                [5, 3, 0, 0, 7, 0, 0, 0, 0],
                [6, 0, 0, 1, 9, 5, 0, 0, 0],
                [0, 9, 8, 0, 0, 0, 0, 6, 0],
                [8, 0, 0, 0, 6, 0, 0, 0, 3],
                [4, 0, 0, 8, 0, 3, 0, 0, 1],
                [7, 0, 0, 0, 2, 0, 0, 0, 6],
                [0, 6, 0, 0, 0, 0, 2, 8, 0],
                [0, 0, 0, 4, 1, 9, 0, 0, 5],
                [0, 0, 0, 0, 8, 0, 0, 7, 9],
            ],
        ),
        "sudoku2": (
            "jsr_331/Sudoku2.java",
            [
                [7, 0, 0, 1, 0, 6, 8, 2, 0],
                [0, 0, 3, 0, 0, 0, 0, 0, 0],
                [0, 0, 8, 0, 9, 0, 4, 0, 0],
                [0, 0, 7, 9, 0, 0, 0, 0, 0],
                [0, 0, 0, 0, 5, 3, 0, 1, 0],
                [1, 0, 9, 2, 0, 0, 6, 0, 0],
                [0, 0, 0, 0, 0, 0, 9, 3, 0],
                [0, 0, 0, 5, 0, 0, 0, 0, 2],
                [0, 0, 0, 4, 0, 0, 0, 7, 0],
            ],
        ),
    }
    for name, (source, clues) in grids.items():
        n = len(clues)
        block = isqrt(n)
        m = Model(name, f"{n}x{n} Sudoku, complete upstream clues", dict(size=n, clues=clues))
        m.source_path = source
        m.generator = "scripts/generate_hakank_variants.py"
        cells = m.vector("x", n * n, 1, n)
        m.constraints = [f"{cells[r * n + c]} = {clues[r][c]}" for r in range(n) for c in range(n) if clues[r][c]]
        for r in range(n):
            m.constraints += m.distinct(cells[r * n : (r + 1) * n])
            m.constraints += m.distinct(cells[r::n])
        for row in range(0, n, block):
            for column in range(0, n, block):
                m.constraints += m.distinct(
                    [cells[(row + r) * n + column + c] for r in range(block) for c in range(block)]
                )
        m.goal = "Complete every given clue, with each row, column, and block containing 1..n exactly once."
        m.compact = n > 4
        result.append(m)
    return result


def main():
    catalogue = ROOT / "catalogue.json"
    data = json.loads(catalogue.read_text())
    for model in models():
        entry = next(entry for entry in data["models"] if entry["id"] == model.name)
        source = next(source for source in entry["sources"] if source["path"] == model.source_path)
        url = f"https://github.com/hakank/hakank/blob/{data['upstream_commit']}/{source['path']}"
        file = ROOT / "catalogue" / (model.name + ".ae")
        file.write_text(model.render({"source_url": url}))
        entry.update(
            status="implemented",
            porting_method="mathematical_specification",
            aeon_file=str(file.relative_to(ROOT)),
            instance=model.instance,
            data=model.data,
            variables=model.variables,
            goal=model.goal,
            expected_score=model.optimum,
        )
        entry.pop("porting_error", None)
    catalogue.write_text(json.dumps(data, indent=2) + "\n")


if __name__ == "__main__":
    main()
