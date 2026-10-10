# LiquidHaskell tutorial ports

Executable Aeon translations of selected examples and exercises from the
official [LiquidHaskell tutorial](https://github.com/ucsd-progsys/liquidhaskell-tutorial/tree/077437f37e77d13a28ffabbf9be0330f88055ba6),
pinned at `077437f37e77d13a28ffabbf9be0330f88055ba6`.
The MIT notice is retained in [UPSTREAM-LICENSE](UPSTREAM-LICENSE).
No upstream code is downloaded during testing.

[manifest.json](manifest.json) records original files/symbols, adaptations,
compile/runtime outcomes, and stability for every case. `port` is a translated
example or completed exercise; `mutation` is our deliberately broken variant;
`aeon-companion` tests an Aeon-specific boundary, not a Haskell feature port.

## Run

From the repository root:

```bash
AEONPATH="$PWD/examples/liquidhaskell" uv run python -m aeon examples/liquidhaskell/positive/list_map.ae
AEONPATH="$PWD/examples/liquidhaskell" uv run python -m aeon --runtime-verification examples/liquidhaskell/positive/native_absolute.ae
uv run pytest tests/liquidhaskell_compatibility_test.py -q
```

`LList.ae` is shared by the list ports; configure its import root through
`AEONPATH`. Tests do this themselves, with independent temporary source paths
to avoid persistent-cache shortcuts. All positives compile without term
synthesis and execute with and without runtime verification. Negatives must
produce the specified compiler error, not merely a parser/import failure.
The faulty native case must compile, return a negative unchecked result, and
raise callee blame with runtime verification. Do not run a blanket all-positive
example glob over these folders.

## Correspondence and stability

Labels describe the tested fragment, not API-version guarantees or whole-language
parity. Stable cases have small deterministic contracts; experimental cases
depend on evolving ADT/measure/runtime machinery; research cases exercise
solver-driven inference and may need annotations/qualifiers for larger programs.

Stable cases' acceptance, error kind and execution result are required regression
expectations; intentional changes must update the suite and explain the changed
contract. Experimental/research classifications do not waive test failures:
they limit how far the example's success can be generalized to other programs.

| Fragment | Tutorial examples | Aeon status / adaptation |
|---|---|---|
| Arithmetic | Ch. 3 `zero`, `one`, `abs`, `divide`, `avg2` | Stable: inline predicates, branch checking, nonzero divisor |
| Boolean evidence/assertions | Ch. 3 `isPositive`, `result`, `lAssert`, `yes`, `no` | Stable: equality for equivalence; Int replaces formatted output |
| ADTs | Ch. 6 `safeHead`, `head` | Experimental: total MaybeInt match; explicit unreachable branches rejected |
| Measures | Ch. 7 `size` | Experimental: constructor equations and explicit tail nonnegativity |
| Recursive APIs | Ch. 7 `map`, `reverse`, `go` exercises | Experimental: Int specialization, increment specialization for map, size metrics and accumulator invariant |
| Inference | Aeon companion to Ch. 3 `abs` | Research: predicate hole constrained by a nonnegative client |
| FFI/runtime verification | Aeon companions to Ch. 3 `abs` | Experimental: native body trusted statically; executed calls checked dynamically |
| Diagnostics | Ch. 3 `nonsense`, broken `abs` | Stable: source location, failed predicate, model for an arbitrary bad input |

## Compatibility differences

- Semantic example compatibility only: no Haskell parser, automatic translator,
  or claim of passing the upstream test suite. GHC/LiquidHaskell are not run;
  expected behavior is curated from the tutorial and tested on the Aeon ports.
- Haskell lists become monomorphic `LList`; Maybe becomes `MaybeInt`. Map is
  specialized to increment before translation. This does not establish
  higher-order dependent-return, polymorphism, abstract-refinement, typeclass,
  parametricity, or lazy-evaluation equivalence.
- The tutorial's natural-valued size measure becomes explicit constructor
  equations and a nonnegative tail refinement. The invariant is written out,
  not claimed as automatically inferred. `LList.size` is logical; `LList.count`
  is a separately executable recursion used by main. No user-written axioms
  or unchecked proof helpers are introduced. Constructor refinements remain
  part of the datatype specification used by Aeon's SMT encoding.
- Map and reverse additionally execute with an order-sensitive checksum of
  small fixture elements, so preserving length while computing wrong contents
  does not pass the execution regression.
- Some tutorial chapters disable termination; these recursive ports instead
  provide explicit `decreasing_by [LList.size xs]` metrics.
- LiquidHaskell accepts a dead `head [] = die ...` arm under a nonempty input.
  Aeon rejects the explicit contradictory nil pattern: this difference is a
  negative regression, not identical behavior. The positive safeHead is total,
  with no omitted patterns or generated term holes.
- Arithmetic ports exercise the integer interpreter/SMT fragment, not Haskell
  machine-Int overflow, laziness, floating point, or backend equivalence.
  Division uses positive operands; negative-division parity is not claimed.
- Native implementations are not statically proved. Runtime verification
  covers executed paths only and cannot prove arbitrary uninterpreted predicates.
- Closed contradictions such as `1 : {v:Int | v = 0}` need no free-variable
  assignment; no counterexample string is fabricated. Broken abs separately
  requires a concrete model and both errors require their actual source location.

## Coverage boundaries

The manifest is tested by ordinary pytest/CI. Tests reject orphan fixtures and
require all seven issue #554 categories; no compatibility failures are skipped
or xfailed. This extends, rather than replaces, existing compiler/LSP tests.

Set measures, sorted-list insertion/BSTs, AVL trees, lazy queues, pointer/vector
libraries, general PLE proofs, abstract refinements and the complete upstream
corpus remain outside this curated suite, not silently declared supported.
New ports should include provenance, execution, meaningful negative mutations,
and explicit adaptations/stability classification.
