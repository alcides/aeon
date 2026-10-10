#!/usr/bin/env python3
"""Stream the published MSR JSONL corpus and materialize embedded Aeon tasks."""

import argparse
import json
from pathlib import Path

from aeon.benchmarks.karel import JsonlDataset, fetch_validation, import_split, materialize_from_datasets


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    fetcher = commands.add_parser("fetch-validation", help="Fetch the pinned surviving 2,500-task validation mirror")
    fetcher.add_argument("--out", type=Path, required=True)
    importer = commands.add_parser("import")
    importer.add_argument("--source", type=Path, required=True, help="Extracted published corpus directory")
    importer.add_argument("--out", type=Path, required=True)
    importer.add_argument("--splits", nargs="+", default=["train", "val", "test"])
    importer.add_argument("--examples", type=int, default=6)
    importer.add_argument("--observed", type=int, default=5)
    importer.add_argument(
        "--require-paper-size",
        action="store_true",
        help="Require one million training tasks and 5,000 validation+test tasks",
    )
    materializer = commands.add_parser("materialize")
    materializer.add_argument("--split", type=Path, required=True)
    materializer.add_argument("--out", type=Path, required=True)
    materializer.add_argument("--start", type=int, default=0)
    materializer.add_argument("--count", type=int, help="Default: every task, with no cap")
    args = parser.parse_args()
    if args.command == "fetch-validation":
        print(json.dumps(fetch_validation(args.out)))
    elif args.command == "import":
        sources = []
        for split in args.splits:
            if Path(split).name != split or split in (".", ".."):
                parser.error("split names must be simple filenames")
            paths = [args.source / f"{split}{suffix}" for suffix in (".json", ".jsonl", ".json.gz", ".jsonl.gz")]
            matches = [path for path in paths if path.is_file()]
            if len(matches) != 1:
                parser.error(f"need exactly one JSONL source for {split}: {matches}")
            sources.append((split, matches[0]))
        if len(set(args.splits)) != len(args.splits):
            parser.error("duplicate split names")
        args.out.mkdir(parents=True, exist_ok=False)
        manifests = {}
        for split, source in sources:
            manifest = import_split(source, args.out / split, args.observed, args.examples)
            manifests[split] = manifest
            print(json.dumps({"split": split, **manifest}), flush=True)
        paper_size = (
            args.observed == 5
            and args.examples == 6
            and manifests.get("train", {}).get("tasks") == 1_000_000
            and manifests.get("val", {}).get("tasks", 0) + manifests.get("test", {}).get("tasks", 0) == 5000
        )
        corpus = {"splits": manifests, "paper_size_matches": paper_size, "all_references_validated": False}
        (args.out / "corpus_manifest.json").write_text(json.dumps(corpus, indent=2) + "\n", encoding="utf-8")
        if args.require_paper_size and not paper_size:
            parser.error("imported counts do not match the paper; see corpus_manifest.json")
    else:
        datasets = [JsonlDataset(str(args.split / f"{name}.jsonl")) for name in ("observed", "heldout", "references")]
        total = len(datasets[0])
        if any(len(dataset) != total for dataset in datasets):
            parser.error("converted split has inconsistent task counts")
        stop = total if args.count is None else args.start + args.count
        if args.start < 0 or stop > total or stop <= args.start:
            parser.error("invalid materialization range")
        for index in range(args.start, stop):
            materialize_from_datasets(*datasets, index, args.out / f"{index:07d}")
        print(json.dumps({"materialized": stop - args.start, "out": str(args.out)}))


if __name__ == "__main__":
    main()
