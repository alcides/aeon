"""Render the same specification hints for both text and token LLM adapters.

The prompt guides generation; the shared runtime/type validators still decide
acceptance. In particular, natural language is never treated as a proof.
"""

from aeon.decorators.api import Metadata
from aeon.utils.name import Name


def specification_prompt(metadata: Metadata, target: Name) -> str:
    entry = metadata.get(target, {})
    parts = []
    examples = entry.get("examples", [])
    if examples:
        parts.append("Example assertions:\n" + "\n".join(example.text for example in examples))
    rows = entry.get("csv_examples", [])
    if rows:
        # Keep prompts bounded even when a CSV is large. Every row is still
        # used by the shared objective evaluator, including omitted rows.
        shown = "\n".join(f"{target.name}{tuple(inputs)!r} = {output!r}" for inputs, output in rows[:32])
        parts.append(f"CSV input/output observations ({len(rows)} rows, first {min(32, len(rows))} shown):\n{shown}")
    for goal in entry.get("goals", []):
        if goal.kind == "example":
            continue
        if goal.kind == "property":
            parts.append(f"Property {goal.function.name} must hold on its generated input corpus.")
        elif goal.kind == "constraint":
            parts.append(f"Required constraint: {goal.function.name}.")
        elif goal.kind == "size":
            parts.append("Minimize the expression size of the synthesized body.")
        else:
            direction = "Minimize" if goal.minimize else "Maximize"
            measure = {
                "csv": "error against all CSV observations",
                "cputime": "measured CPU time",
                "energy": "measured energy (CPU-time proxy when unavailable)",
            }.get(goal.kind, f"objective {goal.function.name}")
            parts.append(f"{direction} {measure} ({goal.length} objective components).")
    parts.extend(entry.get("specification_sources", []))
    # Preserve the free-form task at the end, including the existing doc-only
    # prompt shape used by provider integrations.
    parts.append(entry.get("doc", "Satisfy the type and supplied specifications."))
    return "\n".join(parts)
