# Synthesis-backed standard-library properties

`@property` inputs use the same typed grammar walks as `random_search`, with
SMT completion for refined literals. Later argument types are specialized to
earlier choices, so valid dependent inputs are generated directly—not obtained
by repeatedly discarding invalid random tuples. No Hypothesis or native Python
input generator is needed in these Aeon suites.

The six new suites contain 16 laws (460 trials per seed):

| Library | Laws | Suite under `examples/testing/` |
| --- | --- | --- |
| Math | division/remainder reconstruction, gcd/lcm product, binomial symmetry | `math_properties.ae` |
| String | slice composition/length, trim idempotence, repetition length | `string_properties.ae` |
| List | reverse/append law, reverse involution, map composition/distribution | `list_laws.ae` |
| Map | deletion preserves unrelated keys and the original map; distinct writes commute | `map_laws.ae` |
| Set | removal preserves other elements/original set; union/intersection membership | `set_laws.ae` |
| Stack | length and LIFO order after two pushes/pops, with linear disposal | `stack_properties.ae` |

These complement existing unit and property suites, rather than replacing
their concrete boundary cases. Properties compare observable runtime results,
not just restate declared refinements on trusted native functions.

## Example: synthesize a string and its valid slicing domain

```aeon
import String

@property(30)
def prop_slice_composition
    (s:{v:String | 4 <= String.len v && String.len v <= 12})
    (start:{v:Int | 0 <= v && v < String.len s})
    (stop:{v:Int | start <= v && v <= String.len s})
    (cut:{v:Int | start <= v && v <= stop && v < String.len s}) : Bool :=
    String.concat (String.slice s start cut) (String.slice s cut stop) = String.slice s start stop;
```

First the shared SMT completion synthesizes a string meeting the length bound.
Then it solves `start`, `stop`, and `cut` after substituting earlier generated
values. The law checks that splitting a valid slice and concatenating the parts
recovers the original slice. Empty slices are allowed (`start = stop` or
`cut = start/stop`). `cut < len s` is necessary because the standard library's
`slice` requires its start strictly before the end, even for an empty slice.

String completion now uses Z3's string theory, not only the five fixed string
terminals. Unicode model values are decoded as characters, not textual Z3
escapes. Refined base samples are independently validated through the shared
SMT translation: failed completion cannot silently fall back to an invalid
literal. Unsupported/empty base domains fail generation, not pass a property.

The regression suite also runs a deliberately wrong law:
`len(slice s start stop) = stop - start + 1`. It must fail with a counterexample
whose string and bounds still satisfy every precondition. Dependencies are
preserved during shrinking; refined arguments are conservatively not shrunk.

## Containers and resource boundaries

Lists are synthesized as polymorphic `cons`/`nil` constructor trees. Opaque
native Maps/Sets/Stacks cannot be generated as arbitrary constructor trees;
their properties synthesize ordinary elements and construct states using the
actual standard-library operations. The stack property consumes each linear
handle once and discards the final empty stack. Map/Set properties additionally
check that immutable original snapshots were not modified.

Current scope is deliberately bounded. ADT generation has a depth cap and
cleans measure-based refinements from constructor types; it does not promise
arbitrary measure-refined ADT inputs. The SMT sampler considers a bounded
number of models, not a uniform or exhaustive distribution over the domain.
These tests do not cover external-service, filesystem or GPU modules. Passing
sampled laws supplements static verification; it is not a universal proof.

## Run and reproduce

```bash
python -m aeon --test --seed 0 examples/testing/string_properties.ae
pytest tests/stdlib_properties_test.py -q
```

The Python harness checks all six suites at seeds 0 and 17, requires every
property to execute its full trial count without skips, verifies use of the
shared synthesis walk, and tests failure reporting and Unicode decoding.
The existing testing-suite glob and `run_examples.sh` automatically include
the new files. `PropTesting.forAll*` remains available for legacy callers, but
those wrappers use Python random generators and do not provide this dependent
type generation, shrinking or `--test` reporting.
