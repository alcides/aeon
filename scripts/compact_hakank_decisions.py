"""Factor repeated pure decision projections in existing generated models."""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.generate_hakank_examples import share_decision_accesses


if __name__ == "__main__":
    for path in Path("examples/synthesis/hakank/catalogue").glob("*.ae"):
        source = path.read_text()
        updated = share_decision_accesses(source)
        if updated != source:
            path.write_text(updated)
