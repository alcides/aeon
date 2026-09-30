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
#
# Quick smoke:
#
# ```bash
# uv run python -m aeon --no-main -s contata --budget 30 examples/synthesis/cata/synth/mr/even_odd.ae
# uv run python -m aeon --no-main -s contata --budget 20 examples/synthesis/cata/synth/pbe/is_zero.ae
# uv run python -m aeon --no-main -s cata --budget 20 examples/synthesis/cata/synth/rc/double.ae
# ```
#
# **List PDS via CLI** (`length` over `List Int` from `[…]` literals) is supported
# in the version-space *API* (`tests/contata_test.py::test_cata_synthesizes_list_length_pds`)
# but not yet as a stable `.ae` hole — `@example` list literals currently trip SMT
# reflection of `List.nil`. Tracked as follow-up.
#
# ADT-heavy Contata tasks (trees, mirrors, sorted insert, …) remain in
# `../contata/` as checked reference solutions until the version space grows an
# ADT domain — see that README's "Honest status" section.
