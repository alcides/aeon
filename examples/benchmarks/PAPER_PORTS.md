# Functional synthesis paper benchmarks

This corpus contains **1,619 Aeon programs with synthesis holes** from the
available artifacts of the papers below. It includes separate specification and
sketch variants, and substantial overlap between papers: **1,619 is not a count
of distinct algorithms**. These are executable benchmark ports, not a claim that
an Aeon synthesizer solves them, nor a reproduction of the papers' timings.

| Source | Aeon files | Specification carried into Aeon |
| --- | ---: | --- |
| [λ², PLDI 2015](https://github.com/jfeser/L2) | 44 | Original list/tree examples |
| [Smyth, ICFP 2020](https://github.com/uchicago-pl/smyth) | 164 | All visible examples in five suites, with available sketches |
| [DreamCoder, PLDI 2021](https://github.com/ellisk42/ec) | 220 | 217 saved list tasks; 3 regenerated bootstrap tasks |
| [Burst, POPL 2022](https://github.com/amiltner/BurstArtifactEvaluation) | 135 | 45 tasks × example, reference, and logical specifications |
| [Trio, POPL 2023](https://github.com/pslhy/trio) | 120 | 60 tasks × examples and reference properties |
| [Trio, JFP 2025](https://doi.org/10.5281/zenodo.15690878) | 130 | 65 tasks × examples and reference properties from the journal artifact |
| [GuideSyn, ICSE 2026](https://psl.hanyang.ac.kr/assets/pdf/icse26.pdf) | 80 | All artifact `test/auto_gen` example tasks |
| [Para, PLDI 2024](https://doi.org/10.1145/3656381) | 52 | All active reference definitions in the available mirror, with regenerated examples |
| [Hoogle+, POPL 2020](https://github.com/TyGuS/hoogle_plus) | 44 | Type-inhabitation queries |
| [Hectare, ICFP 2022](https://github.com/jkoppel/ecta) | 64 | 45 Hoogle+ and 19 Stack Overflow type-inhabitation queries |
| [SynMem, OOPSLA 2023](https://doi.org/10.5281/zenodo.8325410) | 64 | Bounded memoization-partition tasks from 64 components in 40 benchmark files |
| [ASAC, FSE 2024](https://github.com/AuQWQuA/ASAC) | 136 | Original contest I/O corpora, with token-exact output comparison |
| [Clause2Inv, ISSTA 2025](https://github.com/SoftWiser-group/Clause2Inv) | 366 | 316 linear + 50 nonlinear invariant tasks; three sampled obligations each |

## Running and regenerating

Use a runtime-fitness synthesizer for example and optimization objectives:

```bash
python -m aeon --budget 10 -s random_search examples/benchmarks/l2/length.ae
```

Choose an actual file from `paper-manifest.json`; source task names are preserved
where possible. Type-only Hoogle+/Hectare queries can also use a type-directed
backend. A search timeout is not evidence that a specification is impossible.
To check a completed implementation, replace its hole and run `--test`.

All generated files are checked in. Regeneration requires the source artifacts,
but ordinary compilation does not. From the repository root:

```bash
# Download immutable, checksum-pinned sources and regenerate selected suites.
python -m scripts.paper_benchmarks --sources /tmp/paper-sources --fetch --suite l2 --suite smyth

# Regenerate everything from an existing source directory, without networking.
python -m scripts.paper_benchmarks --sources /tmp/paper-sources

# Run compilation checks for every generated program and semantic regressions.
pytest tests/paper_benchmarks_test.py tests/inferred_function_types_test.py -n 4
```

`--suite` is repeatable; omitting it selects all suites. `--output` selects a
different output directory. Regenerating a subset preserves the other manifest
entries. Source versions, download URLs, and archive SHA-256 values are in
[`sources.json`](../../scripts/paper_benchmarks/sources.json). The importer
parses source languages as data; it does not execute upstream Python/Lisp or
run the SynMem container. SynMem's archive is approximately 2.9 GB, and ASAC's
archive is approximately 527 MB.

`paper-manifest.json` records source-file and generated-file hashes, specification
kind, example/property counts, and translation details. Edit the translators
under `scripts/paper_benchmarks`, then regenerate; do not hand-edit generated
programs. The new libraries are under `aeon/libraries`.

### ASAC's larger datasets

Every ASAC program embeds one complete original example. Its optimization
objective uses **all** original tests, stored as checksum-verified compressed
JSON files. These roughly 245 MB of compressed data are generated, ignored by
Git, and required to evaluate the full objective:

```bash
python -m scripts.paper_benchmarks --sources /tmp/paper-sources --fetch --suite asac
```

Run this from a source checkout. Missing or corrupt datasets produce explicit
errors instead of silently scoring an empty corpus. Each original input and
answer hash is also recorded in the manifest. Whitespace-separated output
tokens must match; this port does not reproduce MiniZinc checking of alternative
valid witnesses or floating-point answer tolerances.

## Translation boundaries

* **Ingredients differ.** Shared Aeon libraries add functions beyond the
  papers' restricted grammars. λ²'s original background/blacklist are recorded
  but not enforced. Compare specification satisfaction separately from search
  time, program size, grammar restrictions, and number of available ingredients.
* **Data representation.** ML naturals remain Peano ADTs; original products and
  constructor payloads are preserved. Lists/trees from ground datasets use
  `Seq`, `RoseTree`, `BinaryTree`, and `LeafTree`. Pattern fallthrough is preserved,
  and branch thunks prevent eager evaluation of unselected reference branches.
* **Reference/logical specifications.** References become `@property(100)`
  checks outside the hole's ingredient scope. This is bounded testing, not
  universal equivalence. Four Burst higher-order logical specifications use
  syntactic equality on named functions; their ports specialize the properties
  over the source's finite named-helper basis, not arbitrary function equality.
* **Type queries.** Hoogle+/Hectare variables become distinct opaque types, and
  Eq/Ord constraints become explicit dictionary functions. Containers holding
  functions use concrete ADTs. These preserve monomorphic inhabitation tasks;
  they do not reproduce the original polymorphic/Haskell inference engine or
  its entire package database. No behavioral examples are invented for them.
* **DreamCoder.** The pinned source has 217 saved tasks and a loader that adds
  three bootstrap tasks, hence 220 here rather than the paper's 218. Bootstrap
  examples use seed 639 and the upstream input distributions/algorithms. The
  separate 174,258-task generated `list_tasks2.json` is not the paper's list
  evaluation corpus and is not counted here.
* **Para.** The available [source mirror](https://github.com/nicolas-abril/para-artifact)
  contains 52 active reference definitions but omits its saved example/test
  files. We generate 60 deterministic examples per definition, including named
  function inputs. These are not the paper's original 10 × 16 examples or its
  59 library configurations. Source behavior is preserved even where names are
  surprising (e.g. `list-take` pads with zeros and `list-sort` deduplicates).
* **SynMem.** For each component, the importer enumerates all assignments and
  prefixes of three small parameter instances (`n=3`, `m=2`, values in the
  declared finite decision domains). Prefixes share a class exactly when they
  have the same depth and accepted suffixes under the declarative constraints.
  The hole computes an integer cache key. `@minimize_int` penalizes each key
  collision between different classes by 100,000 and adds the number of distinct
  keys. This coefficient exceeds the number of fixture states, so an unsound
  collision cannot improve on a sound partition. This is a finite version of
  the partition subproblem, not local-objective synthesis, the original input
  distribution, an unbounded memoization proof, or an end-to-end timing result.
  The artifact's literal constraints are used; filenames are not interpreted
  as substitute LeetCode specifications.
* **Invariants.** Initiation, consecution, and safety become `@property(200)`.
  Random valuations may make implication checks vacuous. Use the upstream SMT
  templates to prove invariants. SMT integer division/modulo use Euclidean
  semantics; real expressions use exact rationals, including Z3's implicit
  floor conversion in `mod (/ count 2) 2`. Division by zero chooses zero, one
  interpretation of an unspecified operation, not a universal SMT guarantee.

## Repairs and exclusions

The importer repairs only identifiable source transcription problems: tuple
annotations on actually curried `fix` definitions; a missing final declaration
separator in GuideSyn's `tree_bonus`; a stray filename and missing lambda arrow
in Trio JFP's `nat_fac_tailcall`; and Smyth's disabled polymorphic postorder
sketch using `Nat` where its tree parameter is `a`. Missing Smyth sketches are
reconstructed as whole-function holes with the available type and examples;
the manifest identifies them.

[`paper-exclusions.json`](paper-exclusions.json) records unavailable or malformed cases.
FAERY's 30 evaluation problems could not be recovered as identifiable machine
readable specifications from the available paper/source material, so they are
not replaced with guessed functions. SynMem's artifact has 40 benchmark files,
whereas the paper reports 42. Para's mirror does not reproduce all of the paper's
library configurations. These gaps are not counted as completed paper suites.

Source attribution and available upstream license notices are in
[`PAPER_NOTICES.md`](PAPER_NOTICES.md). Upstream license status is not inferred where no
license file is supplied.
