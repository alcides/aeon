"""Native ADT specifications for global constraints and bit-vector examples."""

import json
from pathlib import Path

from scripts.generate_hakank_examples import Model


ROOT = Path(__file__).resolve().parents[1] / "examples/synthesis/hakank"


def models():
    result = []

    def new(name, instance, source, data=None):
        m = Model(name, instance, data)
        m.source_path = source
        m.generator = "scripts/generate_hakank_globals.py"
        result.append(m)
        return m

    m = new("allequal", "four values in 0..6, full source domain", "picat/all_equal.pi")
    xs = m.vector("x", 4, 0, 6)
    m.constraints = [f"Vec.allEqual ({m.sequence(xs)})"]
    m.goal = "Find four values in 0..6 that all have the same value."

    m = new("exactly", "four values in 1..4; value in 1..4, occurrence count in 2..3", "picat/exactly.pi")
    xs = m.vector("x", 4, 1, 4)
    m.variables.update(value=[1, 4], occurrences=[2, 3])
    m.constraints = [f"Vec.count value ({m.sequence(xs)}) = occurrences"]
    m.goal = "Synthesize a sequence, a value, and an exact occurrence count of two or three."

    m = new(
        "globalcardinality",
        "five values with frequencies [4,1,0,0,0]",
        "picat/global_cardinality.pi",
        dict(frequencies=[4, 1, 0, 0, 0]),
    )
    xs = m.vector("x", 5, 1, 5)
    sequence = m.sequence(xs)
    m.constraints = [
        f"Vec.count {value} ({sequence}) = {count}" for value, count in enumerate(m.data["frequencies"], 1)
    ]
    m.goal = "Find a sequence containing four ones, one two, and no values three through five."

    m = new("inverse", "self-inverse permutation of six elements, full source go3 instance", "picat/inverse.pi")
    xs = m.vector("x", 6, 1, 6)
    sequence = m.sequence(xs)
    m.constraints = [f"Vec.element ({value} - 1) ({sequence}) = {i + 1}" for i, value in enumerate(xs)]
    m.goal = "Find a permutation p of 1..6 satisfying p[p[i]] = i at every position."

    m = new(
        "derangement",
        "witness search over the source predicate's 1..5 domain; fixed demonstration removed",
        "minizinc/derangement.mzn",
    )
    xs = m.vector("x", 5, 1, 5)
    m.constraints = m.distinct(xs) + [f"{value} != {i + 1}" for i, value in enumerate(xs)]
    m.goal = "Find a permutation of 1..5 with no fixed point."

    m = new(
        "notallequal",
        "witness search over the source 1..3 domain, length five; fixed demonstration removed",
        "minizinc/not_all_equal.mzn",
    )
    xs = m.vector("x", 5, 1, 3)
    m.constraints = [f"Vec.allEqual ({m.sequence(xs)}) = false"]
    m.goal = "Find five values in 1..3 containing at least two distinct values."

    m = new(
        "arithor",
        "source arrays [0,1,0,0,1] and [0,0,0,1,0], search comparison value",
        "minizinc/arith_or.mzn",
        dict(x=[0, 1, 0, 0, 1], y=[0, 0, 0, 1, 0]),
    )
    m.variables = dict(value=[0, 9])
    m.constraints = [f"{x} = value || {y} = value" for x, y in zip(m.data["x"], m.data["y"])]
    m.goal = "Find a value equal to at least one component of every given pair."

    m = new(
        "bitpatterns",
        "16-bit words, including arithmetic right shifts and truncated left shift",
        "z3/bit_patterns.py",
        dict(width=16),
    )
    bits = {word: m.vector(word, 16, 0, 1) for word in ["x", "y", "z"]}
    m.value_types = {name: "Bool" for names in bits.values() for name in names}

    def equal(expression, target, index):
        expected = "true" if (target >> index) & 1 else "false"
        return f"({expression}) = {expected}"

    for i in range(16):
        x, y, z = (bits[word][i] for word in ["x", "y", "z"])
        m.constraints += [
            equal(f"{y} || {x}", 0x49AB, i),
            equal(f"{bits['y'][min(i + 2, 15)]} != {x}", 0x530B, i),
            equal(f"{bits['z'][min(i + 1, 15)]} && {y}", 0x0883, i),
            equal(f"{bits['x'][i - 2] if i >= 2 else 'false'} || {z}", 0x1787, i),
        ]
    m.goal = "Synthesize x,y,z satisfying all four original 16-bit bitwise equations."
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
            porting_method="native_global_constraint",
            aeon_file=str(file.relative_to(ROOT)),
            variables=model.variables,
            value_types=model.value_types,
            instance=model.instance,
            data=model.data,
            goal=model.goal,
        )
        entry.pop("porting_error", None)
    catalogue.write_text(json.dumps(data, indent=2) + "\n")


if __name__ == "__main__":
    main()
