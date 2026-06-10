# Vericoding benchmark harness

Translates a subset of the [Vericoding](https://github.com/Beneficial-AI-Foundation/vericoding-benchmark) Dafny tasks into Aeon and runs them through Aeon's synthesizers. Addresses issue [#194](https://github.com/alcides/aeon/issues/194).

## What's in scope (v1)

99 candidate Dafny tasks (in [`v1_tasks.txt`](v1_tasks.txt)) that satisfy ALL of:

* No sequences, sets (including set literals like `{1,3,5}`), multisets, maps, arrays, reals, chars, strings, classes, traits, datatypes, ghost code, lemmas, while/for loops, `modifies`/`reads`/`decreases`.
* No quantifiers (`forall` / `exists`).
* Preamble contains only `predicate` definitions — no Dafny `function` (which would need full translation of recursion / `var` let-bindings, beyond v1).
* Method arguments and return type are all `int` or `bool`; single return value.

The translator rejects tasks outside the subset with a printed reason (so a task in `v1_tasks.txt` that was later determined to use, say, a typed `forall x: int :: ...` is reported as `rejected` rather than silently mis-translated).

## How translation works

| Dafny | Aeon |
|---|---|
| `int` / `bool` | `Int` / `Bool` |
| `predicate P(args) { body }` | `def P args : Bool := body;` |
| `method M(args) returns (r:T) requires R ensures E` | `def M args (last:Tlast \| R) : {r:T \| E} := ?hole;` |
| `==>` (implication) | `(a) --> (b)` — aeon's `-->` is parsed by the grammar and [registered in the prelude](../../aeon/prelude/prelude.py) |
| `<==>` (iff) | `a = b` (Bool equivalence) |
| `a <= b <= c` (chained) | `(a <= b) && (b <= c)` |
| `f(a, b, c)` (Dafny call) | `(f a b c)` (curried aeon call) |
| `var X := EXPR;` inside predicate body | `let X := EXPR in` |
| `abs(...)` (Dafny built-in) | emitted `def abs (x:Int) : Int := if x >= 0 then x else 0 - x;` |

## Running

```bash
# Fetch + translate a single task (no synth):
uv run python benchmarks/vericoding/run.py --task DD0080_specs --translate-only

# Synthesize one task with a 30s budget:
uv run python benchmarks/vericoding/run.py --task DD0042_specs --budget 30

# Sweep the whole v1 subset, write CSV:
uv run python benchmarks/vericoding/run.py --all --budget 60 --output report.csv
```

Dafny sources are fetched on demand from `raw.githubusercontent.com` and cached under `benchmarks/vericoding/.cache/` (gitignored).

## Known limitations / follow-ups

These are tracked separately from this issue:

* **SMT accepts undefined arithmetic.** `1 % 0`, `5 / 0` are sometimes "synthesized" as solutions because aeon's verifier doesn't constrain divisor-non-zero. Affects pass rates upward.
* **Synthesizer can't handle `if` in specs.** Tasks whose predicates use Dafny's `if-then-else` expression form (e.g. DA0522) trip `AssertionError: Unhandled term If in synth`.

### Resolved

* **`-->` now in prelude.** Logical implication `-->` is registered in [`aeon/prelude/prelude.py`](../../aeon/prelude/prelude.py) (with an `Implies` SMT translation), so refinements may use it directly. The translator emits `(a) --> (b)` instead of desugaring to `(!a) || b`.
* **`!` precedence fixed.** `!a || b` now parses as `(!a) || b` — the grammar gives `!` its own precedence level tighter than the boolean connectives, so no explicit parens around the negated operand are needed.
* **Pretty-printer operand order fixed.** Comparisons such as `y >= 100` now print in source order rather than flipped (`100 >= y`).

## Extending the subset

To grow v1 → v2:

1. Add support for Dafny `function` (top-level pure recursive functions). The `var X := Y;` rewriter already handles let-bindings; the missing piece is recognising the `function ... { body }` block and emitting `def name args : T = body`.
2. Add bounded quantifiers (`forall x :: 1 <= x <= n ==> P(x)`) — these are SMT-supported and aeon's z3 backend should accept them with the right refinement form.
3. Add `seq<int>` mapped to aeon's inductive `List` (already in [`aeon/libraries`](../../aeon/libraries)).
