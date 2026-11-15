# MBPP refinement review

All 427 maintained programs were reviewed against their prompts, reference
implementations, and examples in Google's [sanitized MBPP dataset](https://github.com/google-research/google-research/blob/master/mbpp/sanitized-mbpp.json).
The initial refinement pass strengthened 354 signatures. The subsequent
sequence representation changes below preserve and extend those contracts.
All 1,324 assertions remain represented.

| Contract | Examples |
| --- | --- |
| Inclusive kth-element bounds | 101, 597, 610 |
| Valid ranges, bit positions, and component indices | 170, 228, 304, 306, 413, 644, 799 |
| Nonempty inputs for partial aggregates | 62, 63, 94, 95, 120, 245, 409, 476, 588 |
| Nonzero divisors and positive modulus | 75, 261, 292, 471, 616 |
| Nonnegative dimensions and sequence indices | 14, 17, 67, 80, 82, 234, 583, 608, 752 |
| Preserved, bounded, or derived collection sizes | 4, 8, 12, 108, 240, 251, 262, 578, 587, 726, 750 |
| Counts bounded by inputs or possible pairs | 66, 105, 142, 166, 253, 296, 438, 556, 757, 767 |
| Result ranges and field bounds | 435, 442, 479, 577, 617, 783, 801 |
| String lengths, character indices, and optional characters | 9, 11, 109, 165, 269, 395, 424, 565, 602, 607 |

These refinements complement `@example`; they do not encode every requirement.
For example, list length does not establish ordering, and a nonempty matrix
does not establish its shape. Element-wide list predicates also require
contextual inference that the current literal elaborator does not supply in
all these uses. The ports retain useful scalar and structural contracts
without inserting trusted assertions or assuming the examples exhaust the
input domain.

Sequence-valued tuples now use native `List`. Task 106 accepts arbitrary
input lists and returns their combined length; task 788 returns a list one
element longer than its input. Neither is restricted to the fixture lengths.
Occurrence counting (250), sorting sublists (104), and neighboring addition
(470) likewise use lengths derived from their inputs rather than fixed tuple
arities. HSV results (783) have length three and retain their component bounds.

The existing finite component contracts in tasks 116, 261, 424, and 616 retain
their fixed lengths as explicit list refinements: three nonnegative integers,
four-element division with nonzero divisors, three nonempty strings, and
four-element modulo with nonzero divisors, respectively. Their component
checks use `List.first` and `List.rest`; they are still restricted ports rather
than fully general element-refined list operations.

Task 587's Python list-to-tuple conversion becomes identity. Tasks 758 and 779
use `List` directly as map keys. Heterogeneous fixed records remain records;
task 596 still measures their shallow runtime memory size.

The initial refinement pass left the following signatures unchanged; sequence
ports in this list subsequently received the representation changes above:

- Boolean classifiers, membership, equality, ordering, and regex tasks with
  meaningful positive and negative inputs: 16, 19, 68, 69, 70, 72, 74, 91, 113,
  115, 222, 281, 284, 285, 394, 405, 414, 433, 434, 454, 464, 567, 576, 582,
  605, 643, 737, 741, 744, 751, 756, 759, 760, 771, 775, 787, 790, 794, 804,
  808, 809.
- Unbounded arithmetic, nested aggregates, and numeric transformations without
  a useful additional scalar bound: 65, 397, 419, 590, 594, 606, 614, 615, 784,
  796.
- Structured tuple operations and nested conversions whose useful relations
  need fuller structural specifications: 132, 140, 259, 273, 297, 399, 401, 421,
  429, 445, 470, 579, 580, 720, 785, 791.
- Unicode case conversion, an adverb-formatting task, and optional results:
  431, 477, 557, 584, 624, 755. Case conversion can expand a Unicode string, and
  optional results should continue accepting inputs for which no answer exists.

## Upstream discrepancies and port details

- **223:** Upstream's fourth assertion supplies `[1, 1, 2, 2]` with `n = 5`,
  despite the prompt defining `n` as the array length. The Aeon port corrects
  this to `n = 4`, retaining the expected `false` result, and requires
  `n = List.size arr`. Reported upstream as
  [google-research/google-research#3470](https://github.com/google-research/google-research/issues/3470).
- **723:** The third assertion compares lists of lengths 9 and 13 despite the
  equal-length prompt. The reference implementation uses `zip`. Unequal
  lengths remain valid and the count is bounded by both lengths.
- **612:** The prompt describes two-column inputs, but the third example has
  three columns. The port retains general transposition rather than requiring
  two columns.
- **452:** The prompt calls the result a loss; the implementation and examples
  return a positive gain when the sale price exceeds the cost. The result is
  nonnegative and bounded by the sale price, not the cost.
- **264:** Dog ages in the first two human years can be fractional. The result
  uses `Float`; the original integral example results are written as floating
  literals with the same values.
- **265:** The reference splits into `step` interleaved groups, which may be
  empty. The outer result length is exactly `step`.
- **310:** Whitespace is discarded during conversion, so list size can be
  smaller than string length.
- **437:** Odd positions are removed using one-based indexing. The result has
  floor-half the input length; task 226 instead retains ceil-half.
- **439:** A negative leading integer is valid; the result is not necessarily
  nonnegative.
- **630:** The Cartesian neighborhood includes the original coordinate and
  diagonals, producing nine pairs.
- **769:** The reference returns a symmetric difference, so the result can be
  longer than either input individually.

Task 596 continues measuring shallow runtime memory size, not element count.
Its result is positive without fixing a platform-dependent byte count.
