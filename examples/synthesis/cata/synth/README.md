# Experiment-ready Contata / CATA holes
#
# These files are **synthesis problems** (open `?hole`s) for paper runs. The
# verified Contata reference suite (all 30 `.mls` ports with reference bodies)
# lives in [`../contata/`](../contata/).
#
# | Dir | Contata category | Backend | Notes |
# | --- | --- | --- | --- |
# | `mr/` | Mutual recursion | `-s contata` | Int encoding of even/odd |
# | `pbe/` | Example-driven Int | `-s contata` | isZero predicate |
# | `rc/` | Relational refinements | `-s cata` | liquid-type oracle |
# | `pds/` | Partial data structure | `-s contata` | `llen` over `List Int` |
# | `so/` | Stack Overflow / list→list | `-s contata` | `rev` via nil/cons/append |
#
# Quick smoke:
#
# ```bash
# uv run python -m aeon --no-main -s contata --budget 30 examples/synthesis/cata/synth/mr/even_odd.ae
# uv run python -m aeon --no-main -s contata --budget 20 examples/synthesis/cata/synth/pbe/is_zero.ae
# uv run python -m aeon --no-main -s cata --budget 20 examples/synthesis/cata/synth/rc/double.ae
# uv run python -m aeon --no-main -s contata --budget 30 examples/synthesis/cata/synth/pds/list_length.ae
# uv run python -m aeon --no-main -s contata --budget 60 examples/synthesis/cata/synth/so/list_rev.ae
# ```
#
# **Hygiene:** do not name a hole after a library definition brought in by
# `open` (e.g. avoid `def length` under `open List` — use `llen`). Otherwise
# `@example` may rebind to `List_length` and Contata will see no I/O facts.
#
# ADT-heavy Contata tasks (trees, mirrors, sorted insert, …) remain in
# `../contata/` as checked reference solutions until the version space grows a
# full ADT domain — see that README's "Honest status" section.
