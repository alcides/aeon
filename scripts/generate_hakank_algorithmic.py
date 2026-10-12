"""Native Aeon ports of models whose demonstration compiles to constants."""

import hashlib
import json
from pathlib import Path

from scripts.generate_hakank_examples import Model


ROOT = Path(__file__).resolve().parents[1] / "examples/synthesis/hakank"


def models():
    euler = Model("euler1", "sum multiples of 3 or 5 below 1000")
    euler.generator = "scripts/generate_hakank_algorithmic.py"
    euler.goal = "Synthesize the sum of every natural number below 1000 divisible by 3 or 5."
    euler.variables = {"answer": [0, 1000000]}
    euler.helpers = [
        """
def sumMultiples (limit:Int) (start:Int) (stride:Int) : Int :=
    if start >= limit then 0
    else if stride >= limit then
        if start % 3 = 0 || start % 5 = 0 then start else 0
    else (sumMultiples limit start (stride * 2)) +
         (sumMultiples limit (start + stride) (stride * 2));
"""
    ]
    euler.constraints = ["answer = sumMultiples 1000 0 1"]
    return [euler]


def main():
    catalogue = ROOT / "catalogue.json"
    data = json.loads(catalogue.read_text())
    for model in models():
        entry = next(entry for entry in data["models"] if entry["id"] == model.name)
        source = next(source for source in entry["sources"] if source["path"].endswith("/euler_1.mzn"))
        url = f"https://github.com/hakank/hakank/blob/{data['upstream_commit']}/{source['path']}"
        path = ROOT / "catalogue" / (model.name + ".ae")
        path.write_text(model.render({"source_url": url}))
        entry.update(
            status="implemented",
            porting_method="algorithmic",
            aeon_file=str(path.relative_to(ROOT)),
            variables=model.variables,
            goal=model.goal,
            aeon_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        )
        entry.pop("porting_error", None)
    catalogue.write_text(json.dumps(data, indent=2) + "\n")


if __name__ == "__main__":
    main()
