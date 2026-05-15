# SMT-style synthesis benchmarks

A small collection of classic Z3/SMT constraint puzzles re-expressed as
Aeon synthesis problems.  Each file:

* declares an inductive `mk` constructor whose argument refinements
  bound every variable to a small interval (this constrains the
  synthesis search space),
* exposes the fields through measure functions (the `+ measure ... `
  declarations) so the solution can be referenced by name,
* defines a `..._hole : { x : T | constraints } = ?hole` that the
  synthesizer must fill in.

The constraints are taken verbatim (modulo encoding) from
[Hakan Kjellerstrand's Z3 puzzle collection](https://www.hakank.org/z3/),
referenced in [issue #130](https://github.com/alcides/aeon/issues/130).

| File                  | Source puzzle                                  |
| --------------------- | ---------------------------------------------- |
| `abbots_puzzle.ae`    | Dudeney, Abbot's Puzzle (100 bushels)          |
| `archery_puzzle.ae`   | Sam Loyd, archery target sum                   |
| `bales_of_hay.ae`     | Pairwise weights of five hay bales             |
| `book_buy.ae`         | Kraitchik, Book Buy / who-is-whose-father      |
| `broken_weights.ae`   | Bachet de Meziriac, 40-pound broken weight     |
| `coin_change.ae`      | Coin change, minimize number of coins to 37    |
| `mamas_age.ae`        | Dudeney, Mamma's Age                           |
| `seseman.ae`          | Seseman's Convent (3x3 border-sum puzzle)      |

## Running a benchmark

```bash
uv run python -m aeon --budget 60 -s gp examples/synthesis/smt/abbots_puzzle.ae
```

`--budget` is the synthesis time budget in seconds; `-s` selects the
synthesizer (`gp`, `random_search`, `enumerative`, ...).  The benchmarks
type-check (`-n`) without synthesis as well, which is useful for testing
parser / elaboration changes.
