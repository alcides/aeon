# Synthesis evaluation runner

This repository-owned runner preserves the full example/benchmark inventory,
creates immutable source plans, executes isolated synthesis processes locally or
on Slurm, and records errors, unsupported goals, missing results, and resource
failures separately. It includes the adapters previously used by SynthesisEval.

Use an environment with Aeon and the desired optional backends installed:

```bash
cd benchmarks/synthesis_eval
python scripts/eval.py snapshot --source ../..
python scripts/eval.py plan --config configs/full-diagnostic.json --run runs/diagnostic
python scripts/eval.py run --run runs/diagnostic --workers 8
python scripts/eval.py collect --run runs/diagnostic
python scripts/diagnose.py --run runs/diagnostic
python scripts/analyze.py --run runs/diagnostic
```

For Slurm, use `scripts/eval.py submit --run runs/diagnostic --partition NAME
--concurrency 8` instead of `run`. Concurrency is per array chunk; separate
chunks can run simultaneously. `scripts/run_shard.py` partitions a plan by
`--shard I --shards N`, allowing one N-task array to enforce N total workers.
Completed raw logs are gzip-compressed by the shard runner and remain readable
by the diagnostic script. Existing results are skipped on resumption.

The diagnostic config selects parsed expression holes, five-second searches,
and seed 0 across 17 backends. Parser errors remain in the inventory audit;
refinement-inference holes do not count as missing expressions. LLM services
and single-step demonstration backends are excluded. `filled` means a complete
returned hole mapping, not proof of an optimum or held-out test success.

For real PSB2 data, add `psb2_samples` to a copied config, pointing to the
prepared checksum-pinned sample directory and manifest. Cached held-out samples
are not used for search. The default config does not provision datasets, GPU
services, or external packages. Missing resources remain visible outcomes.

Storage preflight includes concurrent output headroom. In-flight monitoring
checks free capacity and combined logs; an inherited POSIX file-size limit
bounds each regular file. Storage violations are `infrastructure_error`, not
`no_solution`. Shards preserve evidence and record infrastructure checkpoints;
a failed capacity check does not leave a stale trial lock. Compression failures
leave the raw source log intact. External watchdog timeouts stay distinct.

Run harness regressions with `python -m unittest discover -s tests -v`.
Runtime artifacts and datasets are ignored by git; do not modify a snapshot
while trials are using it.
