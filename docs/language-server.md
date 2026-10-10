# Refinements in the language server

Start the server with `python -m aeon --language-server-mode`. Standard LSP
clients receive inferred types/refinements in hover and inlay hints, and errors
and warnings through `textDocument/publishDiagnostics`. No editor extension is
required for hover or diagnostics.

## Proofs and failures

Hover over the body of either definition:

```aeon
def inc (x:Int) : {v:Int | v > x} := x + 1;
def positive (x:Int) : {v:Int | v > 0} := x;
```

`inc` shows an inferred refined type and a **valid** verification obligation.
`positive` is rejected: hover shows the failing obligation and, when available,
a concrete counterexample such as `x = 0`. Diagnostics include machine-readable
`data` with `kind: "refinement"`, `status`, `obligation`, `counterexample`, and
`reason`; clients that do not consume `data` still display the error message.

Statuses describe the actual verification pass:

- `valid`: the solver proved the obligation (an unsatisfiable negation).
- `invalid`: the solver found a satisfiable negation; a counterexample is shown
  when a concrete assignment can be rendered.
- `unknown`: the solver could not decide, for example because of a timeout.
- `unsupported`: translation failed; this is not a proof or a counterexample.

Unknown and unsupported obligations are never accepted as proofs. A failed
conjunction does not imply that every expression in it is wrong: failed
aggregate obligations retain their aggregate status. Successfully verified
conjunctions are split into source-located goals without additional solving.
Proofs are collected during analysis, not reconstructed from a successful parse
or from runtime samples. Cached solver results preserve their original status
and reason. Syntax errors and document edits clear current proof evidence;
last-good type information may remain available while editing.

## Native boundaries and runtime verification

```aeon
def native_abs (x:Int) : {v:Int | v >= 0} := native "abs(x)";
```

The server warns that the Python implementation is trusted rather than
statically checked. Launch with `--runtime-verification` to enable runtime
checking of refined arguments/results when the program runs. The warning
reports whether that mode is enabled, but analysis **does not execute** the
program: it never claims that a runtime contract has passed. Imported native
definitions are not reported at unrelated positions in the current document.

## Custom requests

`aeon/verification` accepts `{"textDocument": {"uri": "file:///path/example.ae"}}`
and returns `uri`, `obligations`, `runtimeVerification`, and `diagnostics`.
Each obligation contains `status`, a source-facing `obligation` string,
`reason`, `counterexample`, a zero-based LSP `range`, `cached`, and `scope`.
Failed multi-goal conjunctions have `scope: "aggregate"` and a null range,
so their first (possibly valid) expression is not incorrectly blamed in hover.
Obligations without a real source location and trivial `true` goals are omitted.
`runtimeVerification` contains `enabled` and `executed` (always false during
analysis). Diagnostics contain `message` and their structured `data`.

The existing `aeon/infoView` request additionally accepts a zero-based
`position`. Its existing target, locals, globals, errors and synthesis options
remain unchanged; additive `proofObligations` and `runtimeVerification` fields
provide the same current-document verification evidence.

These requests are optional client extensions; the standard hover and
diagnostic paths expose the essential information independently.
