"""Generate the 78 reconstructed DACE tasks not published with the paper."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).parents[1]
OUT = ROOT / "examples/synthesis/dace/reconstructed"

# Paper benchmark groups (Section 6): 46 data-imputation tasks, 32 spreadsheet
# computation tasks, and 6 relational data-completion tasks.
GROUP_TOTALS = {"imputation": 46, "spreadsheet": 32, "relational": 6}

# Category totals from Fig. 19 of Wang, Dillig & Singh (OOPSLA 2017), with the
# benchmark group each category belongs to.
CATEGORIES: dict[int, tuple[int, str, str]] = {
    1: (24, "sum previous value and constant", "imputation"),
    2: (9, "copy previous or next value", "imputation"),
    3: (3, "copy the previous value with the same key", "relational"),
    4: (2, "conditional copy", "imputation"),
    5: (3, "group aggregate over a key column", "relational"),
    6: (7, "average non-missing values", "imputation"),
    7: (2, "key-independent max/min", "imputation"),
    8: (2, "linear interpolation", "imputation"),
    9: (13, "spatial copy", "spreadsheet"),
    10: (4, "sum a range", "spreadsheet"),
    11: (1, "count non-missing values", "spreadsheet"),
    12: (2, "sum two cells", "spreadsheet"),
    13: (4, "difference of two cells", "spreadsheet"),
    14: (1, "average two cells to the left", "spreadsheet"),
    15: (1, "range sum minus fixed cell", "spreadsheet"),
    16: (1, "fixed cell minus range sum", "spreadsheet"),
    17: (1, "maximum of previous five cells", "spreadsheet"),
    18: (1, "integer concatenation surrogate", "spreadsheet"),
    19: (1, "linear extrapolation", "spreadsheet"),
    20: (1, "equation over previous and next values", "spreadsheet"),
    21: (1, "multi-criterion completion outside the DSL", "spreadsheet"),
}

# The six published examples (kept under pbe/) occupy one slot each in their
# category; the reconstructed files cover the remaining slots, so reconstructed
# counts are *derived* as paper total minus published count.
PUBLISHED: list[tuple[str, int, str]] = [
    ("examples/synthesis/dace/pbe/locf.ae", 1, "Example 2.1: previous non-missing value plus a constant"),
    ("examples/synthesis/dace/pbe/prev_sameid.ae", 3, "Example 2.2: previous value with the same id (relational)"),
    ("examples/synthesis/dace/pbe/turns.ae", 9, "Example 2.3: up to value 1, then down to first non-zero"),
    ("examples/synthesis/dace/pbe/group_count.ae", 5, "Example 2.4: COUNT of the row's group (relational)"),
    ("examples/synthesis/dace/pbe/fallback.ae", 4, "Example 2.5: previous non-missing else next (conditional)"),
    ("examples/synthesis/dace/pbe/delta.ae", 13, "Fig. 1: difference between two cells (MINUS)"),
]

VALUES = "[-999999, 3, 5, -999999, 9, 12, -999999]"


def specification(category: int) -> tuple[str, str, str, str]:
    """Return imports, extra definitions, examples, and intended expression."""
    if category == 1:
        return (
            "Column, prev_nonmissing",
            "",
            "@example(fill 3 = 7)\n@example(fill 6 = 14)",
            "prev_nonmissing(values, i) + 2",
        )
    if category == 2:
        return (
            "Column, prev_nonmissing",
            "",
            "@example(fill 3 = 5)\n@example(fill 6 = 12)",
            "prev_nonmissing(values, i)",
        )
    if category == 3:
        # ids chosen so the same-key lookup differs from prev_nonmissing/col_at:
        # fill 3 (id 2) must reach back to index 1, not the adjacent index 2.
        return (
            "Column, prev_sameid",
            'def ids : Column := native "[1, 2, 1, 2, 1, 2, 2]";',
            "@example(fill 3 = 3)\n@example(fill 6 = 12)",
            "prev_sameid(ids, values, i)",
        )
    if category == 4:
        return (
            "Column, prev_nonmissing, next_nonmissing, has_prev_nonmissing",
            "",
            "@example(fill 3 = 5)\n@example(fill 6 = 12)",
            "if has_prev_nonmissing(values, i) then prev_nonmissing(values, i) else next_nonmissing(values, i)",
        )
    if category == 5:
        # Examples chosen so counting over `groups` differs from counting
        # (sentinel-)matches over `values`: row 2 is in a group of three.
        return (
            "Column, group_count",
            'def groups : Column := native "[1, 1, 2, 2, 2, 3, 1]";',
            "@example(fill 2 = 3)\n@example(fill 5 = 1)",
            "group_count(groups, i)",
        )
    if category == 6:
        return (
            "Column, mean_nonmissing",
            "",
            "@example(fill 0 = 7)\n@example(fill 3 = 7)\n@example(fill 6 = 7)",
            "mean_nonmissing(values)",
        )
    if category == 7:
        return (
            "Column, max_nonmissing",
            "",
            "@example(fill 0 = 12)\n@example(fill 3 = 12)\n@example(fill 6 = 12)",
            "max_nonmissing(values)",
        )
    if category == 8:
        return (
            "Column, interpolate",
            "",
            "@example(fill 0 = 3)\n@example(fill 3 = 7)\n@example(fill 6 = 12)",
            "interpolate(values, i)",
        )
    if category == 9:
        return (
            "Column, col_at",
            "",
            "@example(fill 1 = 3)\n@example(fill 2 = 5)\n@example(fill 4 = 9)",
            "col_at(values, i)",
        )
    if category == 10:
        return (
            "Column, sum_before",
            "",
            "@example(fill 1 = 0)\n@example(fill 3 = 8)\n@example(fill 6 = 29)",
            "sum_before(values, i)",
        )
    if category == 11:
        return (
            "Column, count_nonmissing_before",
            "",
            "@example(fill 1 = 0)\n@example(fill 3 = 2)\n@example(fill 6 = 5)",
            "count_nonmissing_before(values, i)",
        )
    if category in (12, 13):
        op = "+" if category == 12 else "-"
        result = "5, 8, 14" if category == 12 else "2, 4, 8"
        extra = (
            'def other : Column := native "[1, 2, 3, 4, 5, 6, 7]";'
            if category == 12
            else 'def other : Column := native "[1, 1, 1, 1, 1, 1, 1]";'
        )
        return (
            "Column, col_at",
            extra,
            f"@example(fill 1 = {result.split(', ')[0]})\n@example(fill 2 = {result.split(', ')[1]})\n@example(fill 4 = {result.split(', ')[2]})",
            f"col_at(values, i) {op} col_at(other, i)",
        )
    if category == 14:
        return (
            "Column, prev_nonmissing",
            "",
            "@example(fill 3 = 5)\n@example(fill 6 = 12)",
            "prev_nonmissing(values, i)",
        )
    if category == 15:
        return (
            "Column, sum_before, col_at",
            "",
            "@example(fill 3 = 5)\n@example(fill 6 = 24)",
            "sum_before(values, i) - col_at(values, 1)",
        )
    if category == 16:
        return (
            "Column, sum_before, col_at",
            "",
            "@example(fill 1 = 9)\n@example(fill 3 = 1)",
            "col_at(values, 4) - sum_before(values, i)",
        )
    if category == 17:
        return "Column, max_previous", "", "@example(fill 3 = 5)\n@example(fill 6 = 12)", "max_previous(values, i)"
    if category == 18:
        return (
            "Column, col_at",
            "",
            "@example(fill 1 = 31)\n@example(fill 2 = 52)\n@example(fill 4 = 94)",
            "col_at(values, i) * 10 + i",
        )
    if category == 19:
        return (
            "Column, extrapolate",
            "",
            "@example(fill 0 = 1)\n@example(fill 3 = 6)\n@example(fill 6 = 15)",
            "extrapolate(values, i)",
        )
    if category == 20:
        return (
            "Column, prev_nonmissing, next_nonmissing",
            "",
            "@example(fill 3 = 9)\n@example(fill 6 = 12)",
            "prev_nonmissing(values, i) + (next_nonmissing(values, i) - prev_nonmissing(values, i))",
        )
    return (
        "Column, col_at",
        "# Category 21 is intentionally recorded as not expressible by the paper's DSL.",
        "@example(fill 1 = 3)\n@example(fill 2 = 5)",
        "col_at(values, i)",
    )


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
    assert sum(total for total, _, _ in CATEGORIES.values()) == 84
    assert dict(Counter(group for total, _, group in CATEGORIES.values() for _ in range(total))) == GROUP_TOTALS

    published_per_category = Counter(category for _, category, _ in PUBLISHED)
    published_rows = [
        {
            "file": file,
            "category": category,
            "group": CATEGORIES[category][2],
            "description": paper_ref,
            "status": "published",
        }
        for file, category, paper_ref in PUBLISHED
    ]

    OUT.mkdir(parents=True, exist_ok=True)
    for old in OUT.glob("c*.ae"):
        old.unlink()
    rows = []
    for category, (total, description, group) in CATEGORIES.items():
        count = total - published_per_category.get(category, 0)
        for index in range(1, count + 1):
            name = f"c{category:02d}_{index:02d}.ae"
            path = f"examples/synthesis/dace/reconstructed/{name}"
            (OUT / name).write_text(render(category, index, description), encoding="utf-8")
            rows.append(
                {
                    "id": f"{category}.{index}",
                    "category": category,
                    "group": group,
                    "description": description,
                    "file": path,
                    "status": "reconstructed" if category != 21 else "not-expressible",
                }
            )

    not_expressible = [row for row in rows if row["status"] == "not-expressible"]
    manifest = {
        "suite": "DACE-inspired reconstruction",
        "total_tasks": 84,
        "group_totals": GROUP_TOTALS,
        "summary": {
            "total_tasks": 84,
            "published": len(published_rows),
            "reconstructed_expressible": len(rows) - len(not_expressible),
            "reconstructed_not_expressible": len(not_expressible),
            "expressible_total": len(published_rows) + len(rows) - len(not_expressible),
            "not_expressible_tasks": [row["id"] for row in not_expressible],
        },
        "published_tasks": published_rows,
        "reconstructed_tasks": rows,
        "source": "https://arxiv.org/abs/1707.01469",
        "paper_category_totals": {str(k): v[0] for k, v in CATEGORIES.items()},
        "note": (
            "The original Stack Overflow inputs were not published; these fixtures reconstruct the paper's "
            "category/operator shapes. The six published examples occupy one slot each in categories "
            "1, 3, 4, 5, 9 and 13, so they are excluded from the 78 reconstructed files. Task 21.1 is recorded "
            "as not-expressible and is not counted as a successful reconstruction."
        ),
    }
    (ROOT / "examples/synthesis/dace/reconstructed_manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
