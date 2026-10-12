"""Small native Aeon ports of catalogue models without a MiniZinc source."""

from itertools import combinations
from math import isqrt
import json
from pathlib import Path

from scripts.generate_hakank_examples import Model, disjunction, total


ROOT = Path(__file__).resolve().parents[1] / "examples/synthesis/hakank"


def number(value):
    return str(value) if value >= 0 else f"(0 - {-value})"


def models():
    result = []

    def new(name, instance, source, data):
        model = Model(name, instance, data)
        model.generator = "scripts/generate_hakank_manual.py"
        model.source_path = source
        result.append(model)
        return model

    m = new(
        "12packproblem",
        "packs [7,13], request 20, count limit 1000",
        "cpmpy/12_pack_problem.py",
        dict(packs=[7, 13], target=20),
    )
    counts = m.vector("pack", 2, 0, 1000)
    m.variables["bottles"] = [0, 2000]
    m.constraints = [
        f"bottles = {total([f'{pack} * {count}' for pack, count in zip(m.data['packs'], counts)])}",
        "bottles >= 20",
    ]
    m.minimize("bottles", "Minimize bottles purchased while supplying at least 20 bottles.", 20)

    m = new(
        "17b",
        "4x4 grid, 4 colors (reduced instance of the 17x17 challenge)",
        "cpmpy/17b.py",
        dict(rows=4, columns=4, colors=4),
    )
    cells = m.vector("cell", 16, 0, 3)
    for r1, r2 in combinations(range(4), 2):
        for c1, c2 in combinations(range(4), 2):
            first = cells[r1 * 4 + c1]
            others = [cells[r1 * 4 + c2], cells[r2 * 4 + c1], cells[r2 * 4 + c2]]
            m.constraints.append(disjunction([f"{first} != {other}" for other in others]))
    m.goal = "Color the grid so no axis-aligned rectangle has four corners of one color."

    m = new("donaldgeraldrobert", "base 10, ten distinct digits, full upstream v1", "cpmpy/donald_gerald_robert.py", {})
    letters = list("donalgerbt")
    m.variables = {letter: [1 if letter in "dgr" else 0, 9] for letter in letters}

    def word(text):
        return total([f"{10 ** (len(text) - 1 - i)} * {letter}" for i, letter in enumerate(text)])

    m.constraints = m.distinct(letters) + [f"({word('donald')}) + ({word('gerald')}) = ({word('robert')})"]
    m.goal = "Assign distinct decimal digits with nonzero leading digits so DONALD + GERALD = ROBERT."

    m = new(
        "magichexagon", "normal 19-cell hexagon, line sum 38, upstream symmetry breaking", "cpmpy/magic_hexagon.py", {}
    )
    letters = list("abcdefghijklmnopqrs")
    m.variables = {letter: [1, 19] for letter in letters}
    lines = [
        "abc",
        "defg",
        "hijkl",
        "mnop",
        "qrs",
        "adh",
        "beim",
        "cfjnq",
        "gkor",
        "lps",
        "cgl",
        "bfkp",
        "aejos",
        "dinr",
        "hmq",
    ]
    m.data = dict(lines=lines)
    m.constraints = m.distinct(letters) + [f"{total(list(line))} = 38" for line in lines]
    m.constraints += [f"a < {letter}" for letter in "chlqs"] + ["c < h"]
    m.goal = "Use 1..19 exactly once, with every hexagonal row and diagonal summing to 38."

    data = json.loads((ROOT / "manual_instances.json").read_text())["eq20"]
    m = new("eq20", "20 equations in seven integers in 0..10, full upstream data", "cpmpy/eq20.py", data)
    xs = m.vector("x", 7, 0, 10)
    vector = m.sequence(xs)
    for coefficients, target in zip(data["matrix"], data["targets"]):
        cs = m.sequence([number(c) for c in coefficients])
        m.constraints.append(f"Vec.dot ({cs}) ({vector}) = {number(target)}")
    m.goal = "Find seven integers in 0..10 satisfying all twenty published linear equations."
    m = new(
        "alldifferentreif",
        "four nondecreasing values in 1..4 and their distinctness flag",
        "cpmpy/all_different_reif.py",
        dict(n=4),
    )
    values = m.vector("x", 4, 1, 4)
    m.variables["distinct"] = [0, 1]
    m.value_types["distinct"] = "Bool"
    sequence = m.sequence(values)
    m.constraints = [f"Vec.increasing ({sequence})", f"distinct = Vec.allDifferent ({sequence})"]
    m.goal = "Synthesize a nondecreasing sequence and a Boolean flag equivalent to all its values being distinct."

    m = new(
        "bowlsandoranges",
        "nine oranges in forty bowls, full upstream instance",
        "cpmpy/bowls_and_oranges.py",
        dict(bowls=40, oranges=9),
    )
    positions = m.vector("bowl", 9, 1, 40)
    m.constraints = [f"Vec.strictlyIncreasing ({m.sequence(positions)})"]
    for i, j, k in combinations(range(9), 3):
        m.constraints.append(f"{positions[j]} - {positions[i]} != {positions[k]} - {positions[j]}")
    m.goal = "Choose nine distinct bowl positions with no three in an arithmetic progression; return one placement."

    m = new(
        "2012cmoproblem",
        "a in 2012..10000, b and n in 2..2012; exact prime membership",
        "cpmpy/2012_CMO_problem.py",
        {},
    )
    primes = [n for n in range(2, 2013) if all(n % d for d in range(2, isqrt(n) + 1))]
    m.variables = dict(a=[2012, 10000], b=[2, 2012], n=[2, 2012], p=[2, 2012])
    prime_table = m.sequence(list(map(str, primes)))
    m.constraints = ["a >= b", "p = a - b", "a * b = n * n", f"Vec.contains p ({prime_table})"]
    m.data = dict(primes=primes)
    m.minimize("a", "Minimize a >= 2012 such that a-b is prime and a*b is a perfect square.", 2025)
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
            porting_method="manual",
            aeon_file=str(file.relative_to(ROOT)),
            variables=model.variables,
            instance=model.instance,
            data=model.data,
            goal=model.goal,
            expected_score=model.optimum,
        )
        entry.pop("porting_error", None)
    catalogue.write_text(json.dumps(data, indent=2) + "\n")


if __name__ == "__main__":
    main()
