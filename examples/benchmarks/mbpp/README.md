# MBPP in Aeon

These 427 ports of the [sanitized MBPP dataset](https://github.com/google-research/google-research/blob/master/mbpp/sanitized-mbpp.json)
are maintained directly as Aeon programs. There is no generator. Each file
retains its upstream task number, documents the task with `@doc`, and specifies
its hole with `@example`. All 1,324 upstream assertions are represented;
`example-counts.json` records the assertion count for each task.
Task 223 corrects an upstream length argument from five to four; documented
corrections are listed in the [review notes](refinements.md).

Use standard `List` and list literals for sequences. Nested lists retain their
element types. `Pair`, `Maybe`, `Map`, and `Set` provide the corresponding
standard representations. Python tuples used as sequences also become native
`List` values, without a wrapper. Fixed sequence lengths use refinements such
as `{xs:(List Float) | List.size xs = 3}`. Heterogeneous records retain typed
fields; mixed sequences use explicit sum types. Optional Python results become
`Maybe` values.

Sequence lengths are not fixed merely because the examples use one length:
occurrence counting, neighboring-element operations, concatenation, and
sorting sublists accept variable-length lists. Task 587's list-to-tuple
conversion becomes identity in this representation. Tasks 758 and 779 use
native immutable lists directly as map keys.

Examples use inline literals and constructors. Specification predicates and
any named fixtures are shadowed at the hole, so they do not become synthesis
ingredients. Example expressions can still evaluate them. The normal
standard-library functions remain available.

All 427 task signatures have been reviewed for refinements. Contracts cover
inclusive indices, nonempty aggregates,
nonzero divisors, numeric domains, collection sizes, and result bounds. For
example, task 101 requires `1 <= k && k <= List.size arr`. Top-n selection
still accepts requests larger than its input, and filters and zip operations
retain their empty-input and unequal-length behavior where applicable.

These are partial specifications alongside the examples, not complete proofs
of each algorithm. In particular, size bounds do not establish sortedness,
permutation preservation, rectangular matrices, or the validity of every
parsed string. Tasks with no useful additional contract retain their original
types; inputs are not restricted to the observed fixture values. The
[review notes](refinements.md) record the coverage and upstream discrepancies.

Recursive implementations that rely on their own result contracts need a
termination measure. The checked recursive list tasks declare `decreasing_by`
using list size or the remaining index. Sequence contracts use `List.size`,
`List.first`, and `List.rest`. Fixed record types expose field measures when
their components need contracts. `Pair.first` and `Pair.second` provide the
corresponding standard library measures.

When a library operation directly solves a task, hide its resolved binding
inside the target body. Task 106 hides `List_append`; task 788 hides `List_snoc`;
task 798 hides `List_sum`; task 792 hides `List_length`
and its equivalent length/rank measures. Hiding only an unqualified alias or
using a selective import does not remove the linked library implementation
from the synthesis context.

Unordered assertions compare membership in both directions, preserving the
original Python `set` comparison. Approximate floating-point assertions use
the original relative/absolute tolerances, expressed in Aeon. These predicates
are validation helpers and are hidden from synthesis.

Task 596 uses `System.getSizeOf`: the **shallow memory size in bytes** of the
actual Aeon value's Python runtime object. It does not count elements or
recursively include referenced objects. Expected sizes are measured at runtime
rather than copied from a particular Python ABI. The target has records of
different arities, and `System_getSizeOf` is hidden at its hole.

Run static validation with `pytest tests/mbpp_examples_test.py`. Selected tests
also fill holes with concrete implementations and execute their examples.
`pytest tests/mbpp_refinements_test.py` checks valid and invalid boundaries,
rejects results outside the contracts, and checks tuple field measures.
To attempt a synthesis task:

```sh
python -m aeon --budget 30 -s tdsyn_enumerative examples/benchmarks/mbpp/mbpp_101.ae
```
