# DACE — data-completion examples (FTA paper)

Aeon renderings of the data-completion tasks from **Wang, Dillig & Singh,
"Synthesis of Data Completion Scripts using Finite Tree Automata"** (OOPSLA 2017;
tool **DACE**, [arXiv:1707.01469](https://arxiv.org/abs/1707.01469)). The paper
synthesises spreadsheet data-completion scripts from input/output **examples**
over a DSL that combines *spatial* (cell/range) and *relational* (table)
reasoning, using finite tree automata as a compact version space.

## How the paper maps onto Aeon

Two honest gaps shape this port:

1. **The benchmark suite is not reproducible verbatim.** DACE's 84 benchmarks
   are spreadsheets scraped from online help forums (a supplementary artifact,
   not listed in the paper). These files instead cover the **operation
   categories** the paper describes, one runnable task each.
2. **Spec mechanism.** DACE is programming-by-**example**; Aeon specifies by
   **refinement type**. So the two halves of this directory take the two
   faithful routes:

   * **Worked pipelines** (top level) — the DACE DSL applied to a concrete input
     table, computing the completed result. These execute end-to-end and are the
     faithful rendering of the *DSL and its operators*.
   * **Synthesised completions** (`synth/`) — per-cell data completion run by the
     new **FTA backend** (`--synthesizer fta`): the output cell is a `?hole`
     whose refinement is the completion formula over the (constant) input cells.
     This is the faithful rendering of *FTA synthesis* itself.

The DSL lives in [`libraries/Table.ae`](../../../libraries/Table.ae): the
relational core (`select`, `filter`, `map_column`, `group_by`, `pivot`/`spread`,
`melt`/`gather`, `summary`) was already present; this work added the spatial and
aggregate operators DACE needs — `mutate`, `cell`, `nrow`/`ncol`, `sum_col`/
`mean_col`/`max_col`/`min_col`/`count`, `arrange`, `head`, `cumsum` (running
total), and `join` — and fixed a broken module path in `group_by`/`pivot`/`melt`.

## Worked pipelines (run directly)

```bash
uv run python -m aeon examples/synthesis/dace/<file>.ae
```

| File | DACE category | Operators | Result |
|---|---|---|--:|
| `column_formula.ae` | column arithmetic | `mutate`, `sum_col` | 33 |
| `aggregate_sum.ae` | aggregate (SUM) | `sum_col` | 35 |
| `group_average.ae` | group-by aggregate | `filter`, `mean_col` | 15 |
| `running_balance.ae` | running/cumulative total | `cumsum`, `cell` | 12 |
| `pivot_wide.ae` | reshape long→wide | `pivot`, `cell` | 7 |
| `melt_long.ae` | reshape wide→long | `melt`, `cell` | 8 |
| `filter_aggregate.ae` | conditional aggregate (SUMIF) | `filter`, `sum_col` | 15 |
| `join_lookup.ae` | relational join (VLOOKUP) | `join`, `mutate`, `sum_col` | 41 |

## Synthesised completions (run with the FTA backend)

```bash
uv run python -m aeon --no-main -s fta --budget 10 examples/synthesis/dace/synth/<file>.ae
```

| File | Completion | Synthesised cell |
|---|---|--:|
| `synth/complete_total.ae` | sum of two cells | `?hole: 15` |
| `synth/complete_average.ae` | mean of three cells | `?hole: 10` |
| `synth/complete_max.ae` | max of two cells | `?hole: 8` |

The FTA backend enumerates candidate cells bottom-up, keys each by its value
(observational equivalence), checks the refinement once per value, and extracts
the smallest accepted cell.

## Scope / faithfulness

- The worked pipelines are *executed*, not synthesised — they demonstrate the
  DSL exactly. Synthesising a full table-transformation **script** from I/O
  examples would need example-based (PBE) acceptance over opaque table values,
  which the current FTA backend (refinement/`validate` acceptance) does not do;
  the `synth/` tasks therefore complete at the **cell** level, where the spec is
  SMT-decidable. Adding example-based acceptance to the FTA backend (so it can
  synthesise whole pipelines over `Table`) is a natural follow-up.
- Run on demand; not swept by `run_examples.sh`. A subset is covered by
  `tests/dace_test.py`.
