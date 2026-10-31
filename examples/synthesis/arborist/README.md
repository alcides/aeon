# Lifted interpretation in Aeon

```bash
python -m aeon --no-main --budget 10 -s arborist examples/synthesis/arborist/local.ae
python -m aeon --no-main --budget 10 -s arborist examples/synthesis/arborist/fold.ae
python -m aeon --no-main --budget 10 -s arborist examples/synthesis/arborist/list_fold.ae
python -m aeon --no-main --budget 10 -s arborist examples/synthesis/arborist/list_sum.ae
python examples/synthesis/arborist/benchmark.py
```

`local.ae` synthesizes a body under a lambda whose argument is computed by the surrounding program. `fold.ae` synthesizes the callback of an ordinary Aeon range fold. Each callback invocation receives the previous invocation's output as its accumulator. The returned body satisfies the examples and is checked by Aeon's type/refinement checker and normal evaluator.

The implementation follows the functional-language construction in Section 3 and Appendix A of [Efficient Bottom-Up Synthesis for Programs with Local Variables](https://arxiv.org/abs/2311.03705) (Li et al., POPL 2024). It is an Aeon adaptation, not the paper's web-automation artifact.

## The paper's list fold

[`list_fold.ae`](list_fold.ae) translates Example 3.1 using an inductive linked list and an ordinary recursive left fold. Its sole specification is the original `[1, 2, 4] → 7`. The fold starts at `0` and visits the elements in order. The hole is the scalar callback body:

```aeon
@example(fold_example (.cons 1 (.cons 2 (.cons 4 .nil))) = 7)
def fold_example (xs:IntList) : Int :=
    fold_left (fun acc => fun element => ?body) 0 xs;
```

The paper deliberately permits both `acc + element` (P1) and `acc * 2 + 1` (P2). Both produce the same local observations on this input:

| Accumulator | Element | Result |
| ---: | ---: | ---: |
| 0 | 1 | 1 |
| 1 | 2 | 3 |
| 3 | 4 | 7 |

The synthesizer returns one validated candidate; the regression test checks that both paper programs remain in the surviving language. A single example does not identify list summation uniquely.

[`list_sum.ae`](list_sum.ae) is a separate variant with additional examples: `[] → 0`, `[4] → 4`, and `[2, 3] → 5`. These exclude P2. With the default grammar, synthesis returns `element + acc`; tests check the result on unseen lists, including zero and negative elements. These additional examples are ours, not specifications from the paper. Aeon supplies the fold structure in both files; synthesis fills its callback.

## Representation and invariants

- A grammar nonterminal records the expression type and remaining operation depth. A state is a packed set of constructor transitions, not one representative expression.
- Specializing a state in a concrete binding context partitions exactly its language by output. Child classes are evaluated bottom-up, and all transitions producing an output are retained in that output's class. Equal outputs of different types remain distinct.
- The enclosing interpreter carries the surviving language through applications, local bindings, branches, recursion, and successive examples. In a fold, the previous result supplies the next accumulator and the previous language supplies the next body state. Candidate bodies cannot change between iterations.
- A state specialized in another context is refined further. Thus `element` and `acc + element`, equal when `acc = 0`, can split when `acc` becomes nonzero. No discarded representative must be reconstructed.
- Extraction is lazy and preserves alternatives: if a candidate fits the examples but fails its refinement, other candidates in the same class are still checked.

The packed languages encode the constraints of the paper's growing footprints. Context-indexed evaluation is memoized; footprints need not be duplicated on every state. Within a fixed finite grammar and terminating supported sketch, language partitioning preserves all example-consistent programs. Deadline and resource exhaustion report failure without claiming that no solution exists.

## Supported fragment

The synthesizer fills one Int/Bool expression hole. The enclosing sketch supplies binders and combinators; the algorithm does not synthesize their structure. It interprets pure Core lambdas, applications, `let`/`rec`, conditionals, type-erased annotations and type applications, and the supported prelude operators. There is no combinator-name recognition or manually inferred table of accumulator bindings.

The generated grammar includes the in-scope scalar parameters/locals, integer constants `0`, `1`, `2`, Boolean literals, `+`, `-`, `*`, `==`, `<`, `<=`, `&&`, `||`, `!`, and scalar conditionals. Operators hidden by lexical shadowing are unavailable. There are no generated recursive calls or arbitrary helper applications in the hole. The enclosing sketch may call pure Aeon helpers, including recursive higher-order functions. Examples accept literal Int/Bool or closed registered-constructor inputs, with Int/Bool outputs; there is no implicit example generation in this backend.

Constructors and `match` in the sketch use the compiler's constructor registry and declaration order. The interpreter recognizes the exact generated constructor/eliminator definitions and implements their semantics directly; it does not execute native Python to discover callback contexts. This also supports polymorphic inductives over scalar/constructor values. Tagged inputs come from the existing constructor-example metadata, preserving list structure. Data is bounded to 128 total nodes (including scalar leaves) and depth 32 (root depth zero).

The expression grammar and observational classes remain scalar: ADT-valued holes/results, Float/String leaves, arbitrary foreign/native calls, effects, multiple holes, and optimization decorators are unsupported. Unit-valued shadow bindings are allowed as administrative code. Defaults are operation depth 3, 100,000 packed states, one million interpreter steps, and the CLI wall-clock budget. Integers are limited to 4096 bits to bound arithmetic work. `ArboristSynthesizer(...)` exposes grammar, state, and step limits to Python callers. Compiler validation is synchronous; the final normal-evaluator check uses the existing worker pool with a timeout.

## Compression experiment

`benchmark.py` runs the local lambda, range fold, paper list fold, and disambiguated list sum with compression enabled and disabled. Disabling compression keeps each distinct transition product separate, providing an exhaustive small-grammar baseline. It prints transition products evaluated, merged alternatives, reachable contexts, interpreter steps, and extracted candidates checked. These are search-work counters, not a claim about the original paper's speedups.

Recorded on these examples with the defaults:

| Example | Compression | Transition products | Merges | Interpreter steps |
| --- | --- | ---: | ---: | ---: |
| Local lambda | enabled | 100 | 75 | 72 |
| Local lambda | disabled | 145 | 0 | 72 |
| Range fold | enabled | 216 | 138 | 820 |
| Range fold | disabled | 392 | 0 | 4720 |
| Paper list fold | enabled | 338 | 206 | 1245 |
| Paper list fold | disabled | 471 | 0 | 8170 |
| List sum | enabled | 348 | 209 | 1380 |
| List sum | disabled | 479 | 0 | 8350 |

The regression suite also compares exact solution languages with independent exhaustive syntax enumeration at depths 0–2, for two fold inputs. A separate depth-2 grammar represents 885 expressions with 49 transition products when compressed, versus 909 without compression. Tests check contextual splitting, consistency across repeated calls, and retaining refinement-valid alternatives after a representative is rejected.
