# Fandango-inspired constrained input generation

Nine Aeon examples express structured-input validity as refinement constraints.
Each contains a synthesis hole for a valid value and a completed value checked
against the same constraints.

| Program | Constraints |
| --- | --- |
| [fuzzing_business_time.ae](fuzzing_business_time.ae) | Time within a business-hours window |
| [fuzzing_ipv4.ae](fuzzing_ipv4.ae) | IPv4 octets and exclusions encoded in the source |
| [fuzzing_isbn10.ae](fuzzing_isbn10.ae) | ISBN-10 checksum |
| [fuzzing_iso8601.ae](fuzzing_iso8601.ae) | Calendar date, leap years, and time fields |
| [fuzzing_person.ae](fuzzing_person.ae) | Consistency between age, adult flag, and birth year |
| [fuzzing_rgb_color.ae](fuzzing_rgb_color.ae) | RGB channels and a brightness bound |
| [fuzzing_sorted_triple.ae](fuzzing_sorted_triple.ae) | Strictly ordered values |
| [fuzzing_triangle.ae](fuzzing_triangle.ae) | Positive sides and triangle inequalities |
| [fuzzing_valid_date.ae](fuzzing_valid_date.ae) | Calendar-valid dates |

The source headers attribute the inspiration to Fandango. These are local Aeon
adaptations, rather than imported Fandango grammars or its experimental corpus.
They synthesize constrained records, without a coverage-guided fuzzing loop or
an external system under test.

Run from the repository root:

```bash
python -m aeon --check --no-main examples/benchmarks/fandango/fuzzing_isbn10.ae
python -m aeon --no-main --budget 30 -s gp examples/benchmarks/fandango/fuzzing_isbn10.ae
```
