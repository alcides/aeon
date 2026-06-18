# SRBench ground-truth symbolic-regression benchmarks

This folder contains aeon synthesis examples for the **ground-truth** half of
[SRBench](https://cavalab.org/srbench/) (La Cava et al., 2021) — the datasets
whose true generating equation is known, so they can be expressed as a program
to be *rediscovered*:

| Source | Count | Description |
|---|---|---|
| **Feynman** | 120 | Equations from the Feynman Lectures, via the [Feynman Symbolic Regression Database](https://space.mit.edu/home/tegmark/aifeynman.html) (Udrescu & Tegmark, 2020). Sampling ranges follow the [SRSD reformulation](https://github.com/omron-sinicx/srsd-benchmark) (Matsubara et al., 2022). Files `feynman_*.ae`. |
| **Strogatz** | 14 | Two-state nonlinear ODE systems from the [ODE-Strogatz repository](https://github.com/lacava/ode-strogatz) (La Cava et al., 2016). Each file recovers one state derivative `f(x, y)`. Files `strogatz_*.ae`. |

SRBench's other ~122 datasets are **black-box** (real-world / synthetic data
with no closed-form model), so there is no target program to synthesize and
they are not represented here.

## Format

Every file follows the same `native`-fitness convention used by the PSB2
examples (e.g. `examples/PSB2/.../gcd.ae`):

```aeon
def sr_errors : (func: (a0:Float) -> ... -> Float) -> Float :=
    fun func => native "...mean absolute error of func vs the true equation
                      over sampled points, computed with numpy...";

@minimize_float(sr_errors synth)
def synth (<vars>:Float) ... : Float := (let sr_errors := unit in ?hole)
```

- The true equation and the sampling are computed inside a self-contained
  `native` Python expression using only the standard library
  (`__import__('math')` / `__import__('random')`), so no third-party
  dependency (e.g. numpy) or external data file is needed.
- Fitness is the mean absolute error over 30 sampled points (`0.0` is a perfect
  fit), minimized.
- `sr_errors` is shadowed inside the hole so the synthesizer builds the
  expression from float primitives (`+`, `-`, `*`, `/`, constants, inputs)
  rather than calling the scorer.

## Running

```bash
uv run python -m aeon --budget 60 -s gp examples/synthesis/srbench/feynman_i_6_20.ae
```

These are **not** part of the default `run_examples.sh` sweep (that glob is
non-recursive and does not descend into this subfolder), because there are 134
of them and they are intended for longer synthesis runs than the 10-second CI
budget. Each file is nonetheless verified to parse, type-check, and drive the
GP engine.
