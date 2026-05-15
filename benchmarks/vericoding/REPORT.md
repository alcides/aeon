# Vericoding v1 — Aeon synthesis report

Tasks attempted: **99**
Synthesizer:     `tdsyn_enumerative`
Median per-task wall time: 7.8s (budget + ~3s aeon startup)

## Overall

| status | count | % |
|---|---:|---:|
| pass | 59 | 59.6% |
| fail-synth | 32 | 32.3% |
| fail-parse | 2 | 2.0% |
| rejected | 6 | 6.1% |
| error | 0 | 0.0% |

**Pass rate: 59.6%**

## By source prefix

| prefix | total | pass | fail-synth | fail-parse |
|---|---:|---:|---:|---:|
| DA | 4 | 1 | 2 | 1 |
| DD | 75 | 48 | 24 | 0 |
| DH | 1 | 0 | 0 | 1 |
| DJ | 3 | 3 | 0 | 0 |
| DS | 1 | 1 | 0 | 0 |
| DT | 2 | 0 | 0 | 0 |
| DV | 13 | 6 | 6 | 0 |

## Parse/type failures (2)

| task | detail |
|---|---|
| `DA0522_specs` | `parse/type-error: AssertionError: Unhandled term (if (((<)[Int ] x⁹) a¹⁰) then 0 else 10) in synth. Type: <class 'aeon.c` |
| `DH0140_specs` | `parse/type-error: AssertionError: Could not infer the type of ΛρValidInput⁵:(Int ).((\n¹⁰ -> ?hole¹³)) for synthesis.` |

## Degenerate passes (27)

These solutions are technically accepted by aeon's verifier but involve undefined arithmetic (`x % 0`, `x / 0`, `x / -1`). They are a known aeon SMT-completeness gap, not a translator issue.

| task | synthesized |
|---|---|
| `DA0069_specs` | `0 / 0` |
| `DD0053_specs` | `-5 % 0` |
| `DD0109_specs` | `-5 % 0` |
| `DD0439_specs` | `-5 % 0` |
| `DD0647_specs` | `-3 % 0` |
| `DD0650_specs` | `-4 % 0` |
| `DD0657_specs` | `-5 % 0` |
| `DD0661_specs` | `-4 % 0` |
| `DD0671_specs` | `-4 % 0` |
| `DD0678_specs` | `-3 % 0` |
| `DD0682_specs` | `-3 % 0` |
| `DD0691_specs` | `-4 % 0` |
| `DD0692_specs` | `1 % 0` |
| `DD0693_specs` | `-4 % 0` |
| `DD0694_specs` | `5 % 0` |
| `DD0698_specs` | `-4 % 0` |
| `DD0702_specs` | `0 % 0` |
| `DD0722_specs` | `-5 % 0` |
| `DD0724_specs` | `3 % 0` |
| `DD0740_specs` | `-4 % 0` |
| `DD0772_specs` | `-3 % 0` |
| `DD0778_specs` | `-5 % 0` |
| `DD0794_specs` | `-8 % 0` |
| `DD0818_specs` | `-3 % 0` |
| `DD0825_specs` | `0 % 0` |
| `DJ0134_specs` | `-5 % 0` |
| `DJ0147_specs` | `-3 % 0` |
