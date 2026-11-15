# Benchmark examples

Paper-based programs and named benchmark collections live in `examples/benchmarks/<benchmark_name>/`.
Names identify the source suite, independently of which Aeon synthesizer can run it. Keep specifications,
reference programs, data, helpers, source notices, and provenance together in the suite directory.

These directories include both direct ports and adaptations. A directory name does not imply reproduction
of the original grammar, inputs, search, or evaluation protocol; consult its provenance notes.

| Directory | `.ae` files | Source | Scope |
| --- | ---: | --- | --- |
| [absynthe/](absynthe/) | 0 | Absynthe string artifact | 27 upstream `.sl` fixtures; see its README and `artifact.json`. |
| [arc/](arc/) | 7 | ARC-inspired grid transformations | Locally encoded fixed grids; original ARC task identifiers are not recorded. |
| [arborist/](arborist/) | 1 | Lifted interpretation (POPL 2024) | Example 3.1 only; local variants remain in `examples/synthesis/arborist/`. |
| [asac/](asac/) | 136 | ASAC (FSE 2024) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [autonumerics/](autonumerics/) | 3 | AutoNumerics-Zero | Reference expressions and adapted approximation tasks; sampled fitness. |
| [bnsynth/](bnsynth/) | 38 | BNSynth | Published bounded-Boolean corpus with pinned upstream Verilog. |
| [burst/](burst/) | 135 | Burst (POPL 2022) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [clause2inv/](clause2inv/) | 366 | Clause2Inv (ISSTA 2025) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [contata/](contata/) | 39 | Contata (CAV 2024) | 30 reference ports in `reference/`; 9 hole-bearing variants in `synth/`. |
| [dace/](dace/) | 99 | DACE (OOPSLA 2017) | Published examples and explicitly labeled reconstructions; see README. |
| [denser/](denser/) | 4 | DENSER | Architecture/grammar adaptations; see `provenance.json` and README. |
| [dreamcoder/](dreamcoder/) | 220 | DreamCoder (PLDI 2021) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [equational_reasoning/](equational_reasoning/) | 8 | Theorem Proving for All (Haskell 2018) | Proof ports, helpers, and negative controls; see manifest. |
| [fandango/](fandango/) | 9 | Fandango-inspired constrained input generation | Local refinement-based examples; see suite README for scope. |
| [grover/](grover/) | 1 | Grover circuit evolution | Paper-derived circuit grammar and simulator; see source header. |
| [guide/](guide/) | 80 | GuideSyn (ICSE 2026) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [hakank/](hakank/) | 945 | Hakan Kjellerstrand's constraint-programming collection | Catalogue ports with source and coverage metadata. |
| [hakank_z3/](hakank_z3/) | 8 | Hakan Kjellerstrand's Z3 puzzle collection | Eight puzzle ports; distinct from the CP catalogue. |
| [hectare/](hectare/) | 64 | Hectare / ECTA (ICFP 2022) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [hoogle/](hoogle/) | 44 | Hoogle+ (POPL 2020) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [image_selection/](image_selection/) | 6 | Synthesizing Optimal Object Selection Predicates for Image Editing using Lattices | Six scenario adaptations, including locally constructed examples. |
| [koza/](koza/) | 3 | Koza genetic-programming benchmarks | Even-3 parity, 6-input multiplexer, and quartic regression instances. |
| [l2/](l2/) | 44 | λ² (PLDI 2015) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [mbpp/](mbpp/) | 427 | Mostly Basic Python Problems | Maintained Aeon ports with standard collections and 1,324 `@example` assertions. |
| [pagie1/](pagie1/) | 1 | Pagie & Hogeweg symbolic regression | Pagie-1 target function; sampling/representation described in source. |
| [para/](para/) | 52 | Para (PLDI 2024) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [property_testing/](property_testing/) | 6 | Property-based testing / conceptual mutation testing papers | Six tasks; each file identifies its source paper and specification. |
| [psb2/](psb2/) | 65 | Program Synthesis Benchmark 2 | Native lists, refined task signatures, typed dataset fitness, and 25 Aeon references; see the [port notes](psb2/README.md). |
| [rlmcts/](rlmcts/) | 1 | RL-MCTS backend demos | One Aeon refinement-synthesis demo and one SMT-LIB training fixture. |
| [smyth/](smyth/) | 164 | Smyth (ICFP 2020) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [srbench/](srbench/) | 134 | SRBench | 120 Feynman and 14 Strogatz expressions. |
| [symetric/](symetric/) | 47 | SyMetric inverse CSG | 47 scenes plus target images, metric helper, and generator. |
| [syngar/](syngar/) | 119 | BLAZE / SYNGAR (POPL 2018) | 109 SyGuS strings in `strings/`; 10 reconstructed matrix tasks in `matrix/`. |
| [synmem/](synmem/) | 64 | SynMem (OOPSLA 2023) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [synquid/](synquid/) | 64 | Synquid (PLDI 2016) | 64 translated programs; fidelity and limitations documented in README. |
| [trio/](trio/) | 120 | Trio (POPL 2023) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [trio-jfp/](trio-jfp/) | 130 | Trio journal artifact (JFP 2025) | Generated artifact ports; see [paper-port documentation](PAPER_PORTS.md). |
| [typestate/](typestate/) | 33 | Plaid, Plural, and Obsidian papers | Models and positive/negative cases; manifest distinguishes original and derived examples. |

Counts are files, including variants, references, helpers, and negative controls, not distinct tasks.

## Shared paper importer

The 13 suites generated by `scripts/paper_benchmarks` share [paper-manifest.json](paper-manifest.json),
[paper-exclusions.json](paper-exclusions.json), [PAPER_NOTICES.md](PAPER_NOTICES.md), and
[paper-licenses/](paper-licenses/). Their 1,619 programs and regeneration instructions are documented
in [PAPER_PORTS.md](PAPER_PORTS.md). That manifest covers only those 13 suites.

Other suites retain their own manifests, generators, and source attributions.

## Running

Run commands from the repository root; for example:

```bash
python -m aeon --check --no-main examples/benchmarks/synquid/List-Null.ae
python -m aeon --budget 30 -s synquid examples/benchmarks/synquid/List-Null.ae
```

`run_examples.sh` discovers `.ae` files recursively and checks benchmark programs without running synthesis.
It preserves the expected rejection behavior of negative examples. See [benchmark usage](../../docs/benchmarks.md).

## Awaiting organization

The 11 pre-existing `bench_*.ae` files directly in this directory are Aeon microbenchmarks,
without an external suite attribution. Their placement is unchanged pending a decision about local examples.
They and the other non-benchmark example groups are listed in [ORGANIZATION.md](../ORGANIZATION.md).

The separate [Vericoding harness](../../benchmarks/vericoding/README.md) fetches and translates tasks on demand;
it has no checked-in Aeon programs to relocate. The [Karel importer](../synthesis/karel/README.md)
also handles external published datasets; its checked-in programs are local regression tasks.
