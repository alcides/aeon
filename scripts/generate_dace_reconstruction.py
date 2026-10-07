"""Generate the 78 reconstructed DACE tasks not published with the paper."""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).parents[1]
OUT = ROOT / "examples/synthesis/dace/reconstructed"

# Counts from Fig. 19 of Wang, Dillig & Singh (OOPSLA 2017).
CATEGORIES = {
    # Six published examples are kept in pbe/; these counts are the remaining
    # 78 reconstructed tasks (the paper's original category totals are in the
    # README and manifest metadata).
    1: (23, "sum previous value and constant"), 2: (8, "copy previous or next value"),
    3: (2, "copy a related cell"), 4: (1, "conditional copy"), 5: (2, "sum previous value and constant"),
    6: (7, "average non-missing values"), 7: (2, "key-independent max/min"), 8: (2, "linear interpolation"),
    9: (12, "spatial copy"), 10: (4, "sum a range"), 11: (1, "count non-missing values"),
    12: (2, "sum two cells"), 13: (4, "difference of two cells"), 14: (1, "average two cells to the left"),
    15: (1, "range sum minus fixed cell"), 16: (1, "fixed cell minus range sum"),
    17: (1, "maximum of previous five cells"), 18: (1, "integer concatenation surrogate"),
    19: (1, "linear extrapolation"), 20: (1, "equation over previous and next values"),
    21: (1, "multi-criterion completion outside the DSL"),
}

VALUES = "[-999999, 3, 5, -999999, 9, 12, -999999]"


def specification(category: int) -> tuple[str, str, str, str]:
    """Return imports, extra definitions, examples, and intended expression."""
    if category in (1, 5):
        return "Column, prev_nonmissing", "", "@example(fill 3 = 7)\n@example(fill 6 = 14)", "prev_nonmissing(values, i) + 2"
    if category == 2:
        return "Column, prev_nonmissing", "", "@example(fill 3 = 5)\n@example(fill 6 = 12)", "prev_nonmissing(values, i)"
    if category in (3, 9):
        return "Column, col_at", "", "@example(fill 1 = 3)\n@example(fill 2 = 5)\n@example(fill 4 = 9)", "col_at(values, i)"
    if category == 4:
        return "Column, prev_nonmissing, next_nonmissing, has_prev_nonmissing", "", "@example(fill 3 = 5)\n@example(fill 6 = 12)", "if has_prev_nonmissing(values, i) then prev_nonmissing(values, i) else next_nonmissing(values, i)"
    if category == 6:
        return "Column, mean_nonmissing", "", "@example(fill 0 = 7)\n@example(fill 3 = 7)\n@example(fill 6 = 7)", "mean_nonmissing(values)"
    if category == 7:
        return "Column, max_nonmissing", "", "@example(fill 0 = 12)\n@example(fill 3 = 12)\n@example(fill 6 = 12)", "max_nonmissing(values)"
    if category == 8:
        return "Column, interpolate", "", "@example(fill 0 = 3)\n@example(fill 3 = 7)\n@example(fill 6 = 12)", "interpolate(values, i)"
    if category == 10:
        return "Column, sum_before", "", "@example(fill 1 = 0)\n@example(fill 3 = 8)\n@example(fill 6 = 29)", "sum_before(values, i)"
    if category == 11:
        return "Column, count_nonmissing_before", "", "@example(fill 1 = 0)\n@example(fill 3 = 2)\n@example(fill 6 = 5)", "count_nonmissing_before(values, i)"
    if category in (12, 13):
        op = "+" if category == 12 else "-"
        result = "5, 8, 14" if category == 12 else "2, 4, 8"
        extra = 'def other : Column := native "[1, 2, 3, 4, 5, 6, 7]";' if category == 12 else 'def other : Column := native "[1, 1, 1, 1, 1, 1, 1]";'
        return "Column, col_at", extra, f"@example(fill 1 = {result.split(', ')[0]})\n@example(fill 2 = {result.split(', ')[1]})\n@example(fill 4 = {result.split(', ')[2]})", f"col_at(values, i) {op} col_at(other, i)"
    if category == 14:
        return "Column, prev_nonmissing", "", "@example(fill 3 = 5)\n@example(fill 6 = 12)", "prev_nonmissing(values, i)"
    if category == 15:
        return "Column, sum_before, col_at", "", "@example(fill 3 = 5)\n@example(fill 6 = 24)", "sum_before(values, i) - col_at(values, 1)"
    if category == 16:
        return "Column, sum_before, col_at", "", "@example(fill 1 = 9)\n@example(fill 3 = 1)", "col_at(values, 4) - sum_before(values, i)"
    if category == 17:
        return "Column, max_previous", "", "@example(fill 3 = 5)\n@example(fill 6 = 12)", "max_previous(values, i)"
    if category == 18:
        return "Column, col_at", "", "@example(fill 1 = 31)\n@example(fill 2 = 52)\n@example(fill 4 = 94)", "col_at(values, i) * 10 + i"
    if category == 19:
        return "Column, extrapolate", "", "@example(fill 0 = 1)\n@example(fill 3 = 6)\n@example(fill 6 = 15)", "extrapolate(values, i)"
    if category == 20:
        return "Column, prev_nonmissing, next_nonmissing", "", "@example(fill 3 = 9)\n@example(fill 6 = 12)", "prev_nonmissing(values, i) + (next_nonmissing(values, i) - prev_nonmissing(values, i))"
    return "Column, col_at", "# Category 21 is intentionally recorded as not expressible by the paper's DSL.", "@example(fill 1 = 3)\n@example(fill 2 = 5)", "col_at(values, i)"


def render(category: int, index: int, description: str) -> str:
    imports, extra, examples, intended = specification(category)
    return f'''# Reconstructed DACE benchmark {category}.{index}
# Category: {description}
# The original Stack Overflow input was not published with the paper. This
# runnable fixture reconstructs the category/operator shape from Fig. 19.
# It is not a claim about the original spreadsheet.
# Run: python -m aeon --no-main -s fta --budget 30 examples/synthesis/dace/reconstructed/c{category:02d}_{index:02d}.ae

import Dace ({imports})

def values : Column := native "{VALUES}";
{extra}
{examples}
def fill (i: Int) : Int := ?hole;

# Intended reconstruction shape: {intended}
'''


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    for old in OUT.glob("c*.ae"):
        old.unlink()
    rows = []
    for category, (count, description) in CATEGORIES.items():
        for index in range(1, count + 1):
            name = f"c{category:02d}_{index:02d}.ae"
            path = f"examples/synthesis/dace/reconstructed/{name}"
            (OUT / name).write_text(render(category, index, description), encoding="utf-8")
            rows.append({"id": f"{category}.{index}", "category": category, "description": description, "file": path, "status": "reconstructed" if category != 21 else "not-expressible"})
    manifest = {"suite": "DACE-inspired reconstruction", "total_tasks": 84, "published_tasks": ["pbe/locf.ae", "pbe/prev_sameid.ae", "pbe/turns.ae", "pbe/group_count.ae", "pbe/fallback.ae", "pbe/delta.ae"], "reconstructed_tasks": rows, "source": "https://arxiv.org/abs/1707.01469", "paper_category_totals": {str(k): v[0] + (1 if k in (1, 2, 3, 4, 5, 9) else 0) for k, v in CATEGORIES.items()}, "note": "The original Stack Overflow inputs were not published; these fixtures reconstruct the paper's category/operator shapes."}
    (ROOT / "examples/synthesis/dace/reconstructed_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
