"""Migrate generated vector spines to the generator's bounded 32-item chunks.

Only private tail definitions are inlined; element order, holes and constraints
are unchanged. Referenced tails are retained, including every sequence root.
"""

import re
from pathlib import Path

TAIL = re.compile(r"^def (sequence\d+_tail(\d+)) : \(Vec (\w+)\) := (.*);$")


def compact(source: str) -> str:
    lines = source.splitlines()
    counts: dict[str, int] = {}
    for name in re.findall(r"\bsequence\d+_tail\d+\b", source):
        counts[name] = counts.get(name, 0) + 1
    substitutions: dict[str, str] = {}

    def substitute(match: re.Match[str]) -> str:
        return substitutions.get(match[0], match[0])

    output = []
    for line in lines:
        match = TAIL.fullmatch(line)
        if match:
            name, position, kind, expression = match.groups()
            expression = re.sub(r"\bsequence\d+_tail\d+\b", substitute, expression)
            if int(position) % 32 and counts[name] == 2:
                substitutions[name] = expression
                continue
            line = f"def {name} : (Vec {kind}) := {expression};"
        output.append(line)
    return "\n".join(output) + "\n"


if __name__ == "__main__":
    for path in Path("examples/synthesis/hakank/catalogue").glob("*.ae"):
        source = path.read_text()
        updated = compact(source)
        if updated != source:
            path.write_text(updated)
