#!/usr/bin/env python3
"""Stratified outcome tables and matched comparisons; no causal claims."""

import argparse
import collections
import csv
import itertools
import json
from pathlib import Path
import statistics


def write_csv(path, rows):
    if not rows:
        return
    with path.open("w") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--run", required=True)
    args = p.parse_args()
    run = Path(args.run)
    features = {x["case"]: x for x in json.loads((run / "inventory.json").read_text())}
    results = [json.loads(x.read_text()) for x in (run / "results").glob("*.json")]
    groups = collections.defaultdict(list)
    for row in results:
        f = features[row["case"]]
        strata = {
            k: f[k]
            for k in (
                "suite",
                "uses_int",
                "uses_float",
                "uses_string",
                "uses_list",
                "uses_modulo",
                "uses_disjunction",
                "external_data",
                "fitness",
            )
        }
        strata.update(
            holes="multiple" if f["holes"] > 1 else "one",
            examples="present" if f["examples"] else "absent",
            refinements="present" if f["refinements"] else "absent",
            branches="present" if f["branches"] else "absent",
            lines="<=25" if f["lines"] <= 25 else "26-100" if f["lines"] <= 100 else ">100",
        )
        for feature, value in strata.items():
            groups[(row["algorithm"], feature, str(value))].append(row)
    output = []
    for (algorithm, feature, value), values in sorted(groups.items()):
        counts = dict(collections.Counter(x["status"] for x in values))
        case_rates = collections.defaultdict(list)
        for row in values:
            case_rates[row["case"]].append(row["status"] == "filled")
        times = [x["elapsed_s"] for x in values if x["status"] == "filled"]
        output.append(
            {
                "algorithm": algorithm,
                "feature": feature,
                "value": value,
                "trials": len(values),
                "cases": len(case_rates),
                "macro_filled_rate": statistics.mean(statistics.mean(x) for x in case_rates.values()),
                "median_filled_wall_s": statistics.median(times) if times else None,
                "status_counts": counts,
            }
        )
    write_csv(run / "feature_groups.csv", output)
    by_algorithm = collections.defaultdict(dict)
    for row in results:
        by_algorithm[row["algorithm"]][(row["case"], row["seed"])] = row
    pairs = []
    for a, b in itertools.combinations(sorted(by_algorithm), 2):
        keys = by_algorithm[a].keys() & by_algorithm[b].keys()
        both_filled = [
            (by_algorithm[a][k], by_algorithm[b][k])
            for k in keys
            if by_algorithm[a][k]["status"] == by_algorithm[b][k]["status"] == "filled"
        ]
        a_only = sum(
            by_algorithm[a][k]["status"] == "filled" and by_algorithm[b][k]["status"] != "filled" for k in keys
        )
        b_only = sum(
            by_algorithm[b][k]["status"] == "filled" and by_algorithm[a][k]["status"] != "filled" for k in keys
        )
        pairs.append(
            {
                "a": a,
                "b": b,
                "matched_trials": len(keys),
                "a_only_filled": a_only,
                "b_only_filled": b_only,
                "both_filled": len(both_filled),
                "median_wall_a_minus_b_s_both_filled": statistics.median(
                    x["elapsed_s"] - y["elapsed_s"] for x, y in both_filled
                )
                if both_filled
                else None,
            }
        )
    write_csv(run / "paired_algorithms.csv", pairs)
    print(f"Wrote feature_groups.csv ({len(output)} groups) and paired_algorithms.csv ({len(pairs)} pairs).")


if __name__ == "__main__":
    main()
