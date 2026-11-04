# CATA / Contata benchmarks

Aeon ports of **Contata** (Miltner, Wang, Chaudhuri & Dillig — *Relational
Synthesis of Recursive Programs via Constraint Annotated Tree Automata*).

## Layout

| Path | Role |
| --- | --- |
| [`synth/`](../../benchmarks/contata/synth/) | **Experiment-ready holes** (open `?hole`, runnable with `-s cata` / `-s contata`) |
| [`contata/`](../../benchmarks/contata/reference/) | Full **30-benchmark** Contata artifact transcription (reference solutions + `@property` / `@example` specs) |
| Top-level `*.ae` | Small smoke holes (`double`, `mutual_pbe`, …) kept for unit tests |

## Backends

```bash
# Version space from @example (paper algorithm) — MR / PBE / List PDS:
uv run python -m aeon --no-main -s contata --budget 30 examples/benchmarks/contata/synth/mr/even_odd.ae

# Enumerate-and-typecheck relational refinements — RC micro-holes:
uv run python -m aeon --no-main -s cata --budget 20 examples/benchmarks/contata/synth/rc/double.ae

# Verified Contata reference suite (no synthesis):
uv run python -m aeon --test examples/benchmarks/contata/reference/mutrec/even_odd.ae
```

| Backend | Spec | Strengths | Limits |
| --- | --- | --- | --- |
| `-s contata` | `@example` I/O | Mutual recursion, recursive Int/List folds | Unary Int/Bool/`List Int`; user ADTs out of scope |
| `-s cata` | Relational refinement | Shallow arithmetic relations, conditionals | No version-space MR; no PBE |

## Paper suite vs. what synthesizes today

The Contata artifact has **30** `.mls` files (7 MR + 7 RC + 12 PDS + 4 SO). All
are transcribed under [`contata/`](../../benchmarks/contata/reference/). Of those, the ones that fit the
current version-space domain have **hole** counterparts under [`synth/`](../../benchmarks/contata/synth/)
(Int-encoded even/odd, list length, …). Tree/mirror/sorted-insert ADT tasks stay
as checked references until the domain grows — details in
[`contata/README.md`](../../benchmarks/contata/reference/README.md).

Covered by `tests/cata_test.py` and `tests/contata_test.py`.
