"""Summarize indexed bindings without conflating microbenchmarks and synthesis."""

import argparse
from datetime import datetime, timezone
from importlib.metadata import version
import hashlib
import json
from pathlib import Path
import platform
import statistics


VARIANTS = ("baseline", "indexed")
CASES = ("list_20_bounded", "array_int_fit", "image_key", "knapsack_50")
LABELS = ("List 20", "Array", "Image", "Knapsack 50")


def median(rows, key):
    return statistics.median(row[key] for row in rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--plot", type=Path, required=True)
    parser.add_argument("--implementation-note", help="Explain any source changes made after measurement.")
    args = parser.parse_args()
    reports = {
        kind: json.loads((args.root / kind / "results.json").read_text())
        for kind in ("verification", "synthesis", "containers")
    }
    # Historical input can contain other experiments; retain only this comparison.
    for kind, report in reports.items():
        report["results"] = [
            row
            for row in report["results"]
            if row["variant"] in VARIANTS and (kind != "containers" or row["case"] == "typing_forks")
        ]
    assert len(reports["verification"]["results"]) == 48
    assert len(reports["synthesis"]["results"]) == 24
    assert len(reports["containers"]["results"]) == 18
    hashes = reports["verification"]["implementation_sha256"]
    assert all(report["implementation_sha256"] == hashes for report in reports.values())
    source_root = Path(__file__).resolve().parents[1]
    current_hashes = {path: hashlib.sha256((source_root / path).read_bytes()).hexdigest() for path in hashes}
    if current_hashes != hashes:
        assert args.implementation_note, "Source changed since measurement; document why timings still apply."
    summary = dict(
        generated_utc=datetime.now(timezone.utc).isoformat(),
        baseline=reports["verification"]["baseline"],
        baseline_adjustment="Direct chunk reverse iteration is enabled in both variants.",
        implementation_sha256=hashes,
        reporting_implementation_sha256=current_hashes,
        post_measurement_note=args.implementation_note,
        environment=dict(
            python=reports["verification"]["python"], platform=platform.platform(), z3=version("z3-solver")
        ),
        verification={},
        synthesis={},
        containers={},
        protocol={
            "verification": "Six runs per case and variant; sequential fresh processes; rotating variant order; SMT caches cleared and garbage collected before timing; collection and parsing excluded; GC remains enabled.",
            "synthesis": "Lazy TDSyn enumerative; 3 seeds (0,1,2); 20-second cooperative budgets per run; sequential fresh processes and rotating variant order. Full validation, runtime requirements and objective evaluation remain enabled. Parsing excluded.",
            "containers": "Three repetitions; 256 child scopes; timing excludes parent construction; peak traced Python allocation measured in a separate pass with children retained. These are container operations, not full solver execution.",
        },
        limitations=[
            "Only lazy TDSyn enumerative is benchmarked end-to-end; other solvers share these contexts but may see different gains.",
            "Short cooperative budgets may overrun while finishing a candidate; throughput uses measured synthesis wall time.",
            "Container microbenchmark speedups and allocation savings must not be interpreted as whole-program or process-RSS improvements.",
            "Indexed typing contexts trade additional allocation for faster lookup.",
        ],
    )
    for case in CASES:
        verification, synthesis = {}, {}
        for variant in VARIANTS:
            vs = [r for r in reports["verification"]["results"] if (r["case"], r["variant"]) == (case, variant)]
            ss = [r for r in reports["synthesis"]["results"] if (r["case"], r["variant"]) == (case, variant)]
            assert len(vs) == 6 and all(r["valid"] for r in vs)
            assert len(ss) == 3
            verification[variant] = dict(median_seconds=median(vs, "seconds"), seconds=[r["seconds"] for r in vs])
            solved = [r for r in ss if r["status"] == "solved"]
            synthesis[variant] = dict(
                solved=len(solved),
                median_validated=median(ss, "validated"),
                median_scored=median(ss, "scored"),
                median_seconds=median(ss, "synthesis_seconds"),
                median_validated_per_second=statistics.median(r["validated"] / r["synthesis_seconds"] for r in ss),
                median_first_solution_seconds=median(solved, "first_solution_seconds") if solved else None,
                fronts=[r["front"] for r in ss],
            )
        summary["verification"][case] = verification
        summary["synthesis"][case] = synthesis
        for variant in VARIANTS:
            verification[variant]["speedup"] = (
                verification["baseline"]["median_seconds"] / verification[variant]["median_seconds"]
            )
            base_rate = synthesis["baseline"]["median_validated_per_second"]
            synthesis[variant]["throughput_ratio"] = (
                synthesis[variant]["median_validated_per_second"] / base_rate if base_rate else None
            )
    for case in ("typing_forks",):
        summary["containers"][case] = {}
        for size in (64, 512, 2048):
            stats = {}
            for variant in VARIANTS:
                rows = [
                    r
                    for r in reports["containers"]["results"]
                    if (r["case"], r["size"], r["variant"]) == (case, size, variant)
                ]
                assert len(rows) == 3
                stats[variant] = dict(
                    median_seconds=median(rows, "seconds"), median_peak_bytes=median(rows, "peak_bytes")
                )
            summary["containers"][case][str(size)] = stats
    # Preserve timing/count/quality evidence without repeating 50-element masks.
    summary["trials"] = {
        kind: [{k: v for k, v in r.items() if k != "returned_value"} for r in report["results"]]
        for kind, report in reports.items()
    }
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, indent=2) + "\n")

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np

    fig, axes = plt.subplots(1, 2, figsize=(12, 4.4), layout="constrained")
    for ax, section, key, cases, labels in (
        (axes[0], "verification", "speedup", CASES, LABELS),
        (axes[1], "synthesis", "throughput_ratio", CASES[1:], LABELS[1:]),
    ):
        x = np.arange(len(cases))
        ratios = [summary[section][case]["indexed"][key] for case in cases]
        values = [100 * (1 - 1 / r) if section == "verification" else 100 * (r - 1) for r in ratios]
        ax.bar(x, values, width=0.6, color="#3478b5", label="Indexed bindings")
        ax.axhline(0, color="#303030", linestyle="--", linewidth=1)
        ax.set_xticks(x, labels)
        ax.set_ylim(-2, 12)
        ax.set_ylabel("Improvement over baseline (%)")
        ax.grid(axis="y", alpha=0.2)
        ax.set_axisbelow(True)
    axes[0].set_title("Verification time saved · median of 6 runs")
    axes[1].set_title("Valid synthesis candidates / second\n3 runs × 20 seconds · lazy TDSyn")
    fig.suptitle("Indexed bindings: measured full-run effects", fontsize=14)
    args.plot.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.plot, dpi=170)
    plt.close(fig)
    print(json.dumps({k: summary[k] for k in ("verification", "synthesis", "containers")}, indent=2))


if __name__ == "__main__":
    main()
