# SyGuS PBE-Strings benchmarks (BLAZE / SYNGAR suite)

These `.ae` files are transcriptions of the SyGuS PBE-Strings benchmark suite
(Alur et al. 2015) used to evaluate **BLAZE** in Wang, Dillig & Singh,
*Program Synthesis using Abstraction Refinement* (POPL'18, arXiv:1710.07740) —
the paper behind aeon's `afta` backend.

Each file specifies a function hole with `@example` input/output pairs and is
solved (when solvable) by the AFTA backend's example-driven (PBE) mode:

```bash
uv run python -m aeon --no-main -s afta --budget 60 examples/synthesis/afta/sygus/<file>.ae
```

## How these were produced

`scripts/sygus_to_aeon.py` converts the official `.sl` benchmarks
(https://github.com/SyGuS-Org/benchmarks, `lib/PBE_SLIA_Track`) into this
format. Regenerate or extend the set with:

```bash
python scripts/sygus_to_aeon.py <sygus_PBE_SLIA_dir> examples/synthesis/afta/sygus
```

## Coverage status (work in progress)

The PBE engine (CFTA over the in-scope `String` DSL, observational merging,
predicate-abstraction CEGAR) is correct and solves *substring/slice-extraction*
benchmarks quickly (e.g. `34801680` → `slice s 6 19`, and the hand-written
`../pbe_firstname.ae` → `slice name 0 3`). Full suite coverage is **not yet
complete** and needs:

- **More DSL operators.** aeon's `String` library lacks a few SMT-LIB string
  ops the suite uses (`str.at`, `str.indexof` with a start offset,
  `int.to.str`/`str.to.int`). Benchmarks needing them currently can't be built.
- **Grammar-scoped components.** Each `.sl` carries a grammar restricting the
  usable operators; scoping the synthesiser to that grammar (instead of all of
  `open String`) would shrink the search space dramatically.
- **Deeper / wider search.** Benchmarks whose solution composes several
  operators (`concat` of multiple substrings, index arithmetic) exceed the
  current depth/budget.

Until then, treat this directory as the transcribed benchmark set; the subset
that the backend solves within a given budget will grow as the items above land.
