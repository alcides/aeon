# PSB2 in Aeon

The 25 tasks from [PSB2](https://www.cs.hamilton.edu/~thelmuth/PSB2/PSB2.html)
have 65 maintained Aeon variants: 25 executable reference functions under
`solved/`, 25 multi-objective synthesis files, and 15 other synthesis variants.
The ports follow the [upstream reference implementations at `psb2-v1.0`](https://github.com/thelmuth/Clojush/tree/psb2-v1.0/src/clojush/problems/psb2).

## Representations and ingredients

Functional sequences use native `List`, including nested results. Shopping
prices, discounts, and Euclidean vectors use `List Float`; they are not integer
arrays. Fixed homogeneous results use length refinements: four coin counts,
two parts of a cut vector, two values in find-pair, and two Mastermind counts.
Substitution cipher uses the standard `Map String String` in its reference.
String and list operations come from `String`, `List`, and `Math` rather than
local native wrappers or opaque `Range`, `Zip`, `Dict`, or `Counter` types.

The solved functions are Aeon implementations that can be exported or imported
for testing; they do not contain synthesis holes or require a dataset download.
Their input contracts match the synthesis inputs. Their return annotations
describe representations; the stronger synthesis postconditions are checked
separately and are not claimed as complete static proofs of the references.

`Math_gcd` is hidden at every GCD hole. Root variants that retain a reference
export also hide it. All holes hide the dataset fixture, scoring function, and
the resolved `PSB2Fitness_cases` binding. General building blocks such as
`List.map`, `filter`, `zipWith`, folds, ranges, and string operations stay visible.
Shadowing uses the resolved names, so qualified imports cannot bypass it.

## Contracts

| Task | Additional contracts |
| --- | --- |
| Basement | Nonempty bounded integer list; result is a valid index. |
| Bouncing balls | Positive initial height; smaller positive bounce height; 1–20 bounces; bounded nonnegative distance. |
| Bowling | Scorecard length; score between 0 and 300. |
| Camel case | Result length does not exceed the input length. |
| Coin sums | Four nonnegative counts, denomination bounds, and exact value conservation. |
| Cut vector | Nonnegative input elements; two output lists whose lengths sum to the input length. |
| Dice game | Positive die sizes; probability in `[0, 1)`. |
| Find pair | Two distinct results whose sum is the target. |
| FizzBuzz | Positive input and bounded nonempty result. |
| Fuel cost | Masses in the dataset domain; nonnegative fuel bounded by input size. |
| GCD | Positive result bounded by both inputs and dividing both. |
| Substring indices | Nonempty inputs; every result index fits a full match; bounded result count. |
| Leaders | Bounded elements; result no longer than input and nonempty when input is nonempty. |
| Luhn | Exactly sixteen digits in `[0, 9]`; checksum in `[0, 144]`. |
| Mastermind | Two four-character inputs; two nonnegative counts totaling at most four. |
| Middle character | Nonempty input; result length one or two according to input parity. |
| Paired digits | Input length and maximum possible sum. |
| Shopping | Bounded floating-point prices/discounts; equal lengths; nonnegative total. |
| Snow day | Nonnegative hours/snow/snowfall; melt proportion in `[0, 1]`; nonnegative result and zero-hour identity. |
| Boolean expressions | Nonempty, odd-length expression; Boolean result. |
| Spin words | Preserved string length. |
| Square digits | Nonnegative integer; bounded nonempty output; zero maps to `"0"`. |
| Substitution cipher | Equal alphabet lengths and preserved message length. |
| Twitter | Exact empty/overlong messages and bounded confirmation length. |
| Vector distance | Bounded floating-point elements; equal vector lengths; nonnegative bounded distance. |

Element constraints use `List`'s abstract refinement parameter. These and the
size/number constraints are checked at the dataset boundary before invoking a
candidate. Some dataset guarantees remain semantic assumptions: valid bowling
and Boolean syntax, decimal digit strings, ASCII case-conversion inputs, a
negative prefix for basement, a unique pair for find-pair, and message characters
belonging to the cipher alphabet. The refinements do not fully specify those
properties or prove optimality, ordering, membership, or maximality.

## Fitness and reference details

`PSB2Fitness.cases` samples lazily and deterministically. Each evaluation gets a
fresh snapshot. The Python boundary converts vector columns to native Aeon
lists and converts results back before scoring. Only objective vectors remain
linear `Array Float` values. Fractional errors are retained. Nested outputs are
compared element by element, so different cut vectors with equal sums no longer
receive zero error. Single-objective variants average per-case errors; they do
not join strings across unrelated examples. Multi-objective variants retain
200 objectives, or 50 for the existing leaders variant.

The upstream references settle several details that the older ports missed:

- Shopping returns a floating-point total rounded to two decimal places.
- Snow day computes `snow * (1 - melt) + snowfall` each hour. Its fixed cases
  include a snowfall rate of 15, so the contract does not impose the old cap of 10.
- Leaders include repeated equal maxima. Boolean expressions evaluate strictly
  left to right. Substring matches may overlap.
- Cut vector chooses the last minimum on a nonzero tie, but the first exact
  balance. A one-element vector produces that vector and an empty second part.
- Mastermind returns white then black counts. Coin sums return pennies,
  nickels, dimes, then quarters. Twitter uses the ASCII apostrophe from the data.

`conformance.json` contains hand-maintained upstream fixed cases and small
diagnostic cases derived from these algorithms. It is an offline regression
set, not a replacement for the full published dataset or a generated benchmark.

Run compilation and offline validation with:

```sh
pytest tests/psb2_examples_test.py tests/psb2_stdlib_test.py tests/psb2_refinements_test.py
```

Synthesis evaluates the existing full dataset objectives and may download the
PSB2 datasets on first use through the sampling library:

```sh
python -m aeon --no-main --budget 60 -s synquid examples/benchmarks/psb2/annotations/multi_objective/gcd.ae
```
