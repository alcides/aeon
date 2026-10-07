# Soundness boundaries and the trusted computing base

Aeon separates claims that are proved by the type checker from claims supplied
by the program author or checked only at runtime. A successful type check is
therefore not, by itself, a claim that every external implementation is
correct.

## What is proved

For ordinary Aeon definitions, the checker elaborates types and refinements,
generates verification conditions, and discharges them with the SMT-backed
liquid checker. This includes refinement subtyping, branch/path facts,
constructor reasoning, and the termination obligations for recursive
functions that declare a valid decreasing measure.

Refinement inference proposes facts and qualifiers for those existing
verification conditions. It does not add axioms to the language or to the SMT
context. An obligation that cannot be proved remains an error (or a warning
when an undecidable expression is allowed in non-strict mode).

## What is trusted

The following are explicit trust boundaries:

| Mechanism | What Aeon checks | What remains the author's responsibility |
|---|---|---|
| `axiom name : T` | Syntax and use of the declaration | The declared value and every refinement in `T`; its body is never proved |
| `native "..."` | The surrounding Aeon program and any applicable runtime checks | The Python expression and its declared Aeon type/refinement |
| `native_import "..."` | The import declaration and its use in Aeon | The imported module and Python-side behaviour |
| Uninterpreted predicates/functions | Well-formedness and logical consequences of equalities/premises | Their real-world meaning and any laws not stated in Aeon |
| Opaque types and FFI measures | Refinements expressed over the opaque value | Representation invariants and consistency with Python |

Plain native bindings without a refinement are still executable foreign code,
but they do not contribute a refined logical fact merely because they are
native. A refined native binding is listed as trusted because its postcondition
is an assertion supplied by the binding author.

## What is checked dynamically

`--runtime-verification` enables checks for supported parameter and result
refinements at execution time. A failure is reported with caller/callee blame.
Runtime verification complements static checking; it does not turn an
unchecked `native` implementation into a statically proved implementation.
The option is disabled by default.

## What is skipped or rejected

Liquid predicates are intended to stay in the decidable fragment supported by
the verifier. Aeon reports constructs outside that fragment, such as certain
nonlinear arithmetic, as warnings by default. `--strict-decidable` turns those
warnings into errors. A skipped or unsupported predicate must not be read as a
proof: it is an explicit limitation of the verification result.

Open synthesis holes are also not evidence of a proof. Compilation, runtime
refinement execution, and synthesis reject or defer incomplete programs where
the missing term is needed to establish the relevant claim.

## Auditing a program

Use the trust report to inspect the trusted computing base:

```bash
python -m aeon --trust-report program.ae
python -m aeon --trust-report --trust-for main program.ae
```

The report identifies explicit axioms and refined native bindings, and the
`--trust-for` form restricts the result to assumptions transitively reachable
from a function. A report with no entries means that no explicit axiom or
refined native binding was found in the selected scope; it does not mean that
ordinary Python dependencies or external systems are formally verified.

## Design rule for new features

Reusable predicates, qualifiers, measures, relational refinements, and richer
parameter/result relationships must preserve this accounting:

1. proved facts come from checked definitions and discharged verification
   conditions;
2. dynamic checks are labelled as dynamic checks; and
3. trusted assumptions are explicit, auditable, and visible in the trust
   report.

No feature should silently add a quantified axiom, assume an uninterpreted
function law, or treat an undecidable obligation as proved.
