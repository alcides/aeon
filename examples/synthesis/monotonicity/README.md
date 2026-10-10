# Monotonicity as a synthesis refinement

Five Aeon-native tasks for [issue #567](https://github.com/alcides/aeon/issues/567).
Synthesize **one unary function** and prove its monotonicity over a declared
integer interval. No axioms, native implementations, or sampled-pair fitness:

```aeon
def f (x:{v:Int | (0 - 5) <= v && v <= 5}) : Int := ?body;
def monotonicity
    (x1:{v:Int | (0 - 5) <= v && v <= 5})
    (x2:{v:Int | x1 <= v && v <= 5})
    : {p:Bool | p && f x1 <= f x2} := true;
```

The proof arguments represent **arbitrary** ordered inputs. Its `true` body
inhabits the result refinement only if Aeon proves the two-call relation.
Existing reflection derives the SMT definition of `f` from the actual candidate
body; both calls use that same body. The hole sees `x`, not `x1`/`x2`.
There is no new quantified or higher-order syntax: the two-call property is
expressed by an ordinary dependent refinement witness, not an unsupported
refinement directly over a function value.

## Run

From a repository checkout:

```bash
# Search; positive-offset solutions include x + 1:
uv run python -m aeon.benchmarks.monotonicity --task shift --budget 10

# Prove a piecewise-linear candidate:
uv run python -m aeon.benchmarks.monotonicity --task relu \
  --candidate 'if x <= 0 then 0 else x'

# Disprove a candidate and report an ordered input pair:
uv run python -m aeon.benchmarks.monotonicity --task nondecreasing \
  --candidate '0 - x'

# Attempt all tasks (repeat --task to select a subset):
uv run python -m aeon.benchmarks.monotonicity --budget 10
```

Default backend: Aeon's `enumerative`; `--backend tdsyn_enumerative` selects
type-directed enumeration. The harness calls existing candidate generators and
compiles completed candidates with an SMT-backed validator. It does not implement
a Python expression grammar/evaluator. There is no numerical fitness objective:
**every refinement must be proved**, with a final gate even if a backend ignores
its validator. JSON lines report task, candidate, status, time and failures.
Exit 0 means all selected tasks are proved; exit 2 means a rejection or no solution.
`--task-dir` supplies the `.ae` directory for an installed package/separate checkout.

An unresolved `?body` has no implementation from which to prove monotonicity.
These open specifications intentionally fail ordinary whole-file verification:
**use this harness**, not `python -m aeon task.ae`. It recovers the search scope
and goal from the compiler's partial core, retains the proof contract during
search, and compiles each completed candidate normally. The open specification
is never accepted or reported as verified.

## Tasks

| Task | Domain | Constraints | A valid Aeon body |
|---|---|---|---|
| `nondecreasing` | [-5,5] | `x1 <= x2` implies `f x1 <= f x2` | `0` |
| `strict` | [-5,5] | `x1 < x2` implies `f x1 < f x2` | `x` |
| `identity` | [0,4] | Nondecreasing; `f 0 = 0`, `f 4 = 4` | `x` |
| `shift` | [0,4] | Nondecreasing; `f 0 = 1`, `f 4 = 5` | `x + 1` |
| `relu` | [-5,5] | Nondecreasing, nonnegative; endpoint/origin anchors | `if x <= 0 then 0 else x` |

References are illustrations, not templates fed to search. Endpoints do not
determine the entire function: other solutions satisfying all contracts are valid.
Tests run actual synthesis for the first four tasks and prove all five references.
The piecewise task is harder: a five-second enumerative run did not solve it;
reference validation is not a claim of successful search within every budget.

## Sound fragment and result semantics

Supported: mathematical `Int`, literals, `x`, addition/subtraction, multiplication
with a constant operand, comparisons/Boolean operators and nested conditionals.
Python arbitrary-precision Int and SMT Int agree here. This is **not** continuous
real or floating-point monotonicity. Domains must be shown nonempty; nondecreasing
contracts include both endpoints and equal-input pairs. Strict contracts require
strictly ordered inputs instead.

Division/modulo (even by a nonzero constant), nonlinear products (`x*x`), Float,
holes, helper/self calls, FFI, arbitrary lets and annotations are `unsupported`,
never proofs. `proved` means ordinary verification accepted the complete program.
`disproved` requires a concrete SMT witness to a refinement. Otherwise a failure
is `unproven`, including solver `unknown` or unavailable models; a Boolean failure
alone does not justify a disproof. Counterexamples use the original VC with the
candidate's reflected definition, not an unconstrained/uninterpreted replacement
for `f`. A labelled whole-program witness can relate to either monotonicity or
endpoint constraints, alongside individual failed predicates.

## Shape-constrained symbolic regression

This implements the hard shape-constraint component: fitting endpoints/data cannot
rule out a decreasing segment between observations. A data-fitting objective can
be added separately, but cannot replace the proof. The contextual reference is
[Comparing optimistic and pessimistic constraint evaluation in shape-constrained
symbolic regression](https://doi.org/10.1145/3512290.3528714). These Aeon-native
tasks are **not** a transcription of that paper's dataset or evaluation methods.
