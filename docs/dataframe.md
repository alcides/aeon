# `DataFrame`: pandas frames with an Array column bridge

`DataFrame.ae` is the general tabular API. Backing storage is a pandas
`DataFrame`; refinements track `df_nrows` / `df_ncols`. The type is **linear**.

- Source: [`aeon/libraries/DataFrame.ae`](https://github.com/alcides/aeon/blob/master/aeon/libraries/DataFrame.ae)
- Bindings: [`aeon/bindings/dataframe.py`](https://github.com/alcides/aeon/blob/master/aeon/bindings/dataframe.py)

## Design

| Concern | Engine |
|---------|--------|
| CSV I/O, select, join, groupby, nulls | pandas |
| Dense numeric column kernels | `Array` + `@llvm` / `@gpu` |

Aeon does **not** compile pandas to LLVM. Extract a column with `with_col`,
run an Array kernel, write back with `set_col` (or use `map_col`).

## Linearity helpers

| API | Role |
|-----|------|
| `copy` → `fst_df` / `snd_df` | Split one frame into two independent copies |
| `with_col` → `wc_frame` / `wc_array` | Read a Float column without losing the frame |
| `map_col` | Extract → transform → write back in one call |

## Relation to other modules

| Module | Role |
|--------|------|
| `DataFrame.ae` | General DS / ETL |
| `MLCore.ae` / `Learning*` | ML pipelines (own `DataFrame` opaque + sklearn) |
| `Table.ae` | List-of-dicts relational DSL (synthesis / DaCe) |
| `Array.ae` | Linear host buffers + LLVM/GPU sized kernels (`*_n` / `*_n_int`) |
| `Tensor.ae` | Numpy `Vector` / `Matrix` for NN shapes (not the same as `Array`) |

## Examples

- `examples/dataframe/etl_pipeline.ae`
- `examples/dataframe/feature_llvm.ae`
- `examples/dataframe/groupby_agg.ae`
