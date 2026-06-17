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

## Programming-by-example completions (`pbe/`)

These reproduce the **five motivating examples of Section 2** with the paper's
*actual* mechanism — **programming-by-example**. The hole is a *function of the
missing-cell index*; the spec is concrete input/output rows given with
`@example` (or `@csv_data`). The FTA keys each automaton state by the candidate's
**output vector over the examples** (observational equivalence over the example
set, exactly as in the paper) and composes the DACE primitives — and a
conditional — to reproduce them. The table is a `Column` global (a native list
with a `-999999` missing sentinel); the primitives live in
[`libraries/Dace.ae`](../../../libraries/Dace.ae).

```bash
uv run python -m aeon --no-main -s fta --budget 60 examples/synthesis/dace/pbe/<file>.ae
```

| File | Paper example | Synthesised completion |
|---|---|---|
| `pbe/locf.ae` | 2.1 LOCF +1 | `1 + prev_nonmissing(col1, i)` |
| `pbe/prev_sameid.ae` | 2.2 previous with same id (relational) | `prev_sameid(ids, vals, i)` |
| `pbe/turns.ae` | 2.3 up to value 1, then down to first non-zero | `down_first_nonzero(colC, up_find_value(colB, i, 1))` |
| `pbe/group_count.ae` | 2.4 group total = COUNT | `group_count(groups, i)` |
| `pbe/fallback.ae` | 2.5 previous else next (switch) | `if … then prev_nonmissing(col, i) else next_nonmissing(col, i)` |

The conditional (Example 2.5) uses the FTA's `If` builder; the others are
branch-free. Covered by `tests/dace_test.py::test_fta_pbe_completion`.

## Scope / faithfulness

- The worked pipelines are *executed*, not synthesised — they demonstrate the
  DSL exactly. The `synth/` tasks complete at the **cell** level against a
  refinement spec. The `pbe/` tasks complete a **function of the cell index**
  from input/output **examples** — the paper's programming-by-example mechanism,
  now supported by the FTA backend (it keys states by the output vector over the
  examples). Cell extraction over the relational `Table` value (rather than a
  numeric `Column`) is the remaining step toward whole-pipeline PBE.
- Run on demand; not swept by `run_examples.sh`. Covered by `tests/dace_test.py`.
