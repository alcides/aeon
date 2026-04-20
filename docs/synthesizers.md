# Synthesizers

Aeon supports automatic synthesis of program holes (`?hole`). When a hole is present, a synthesizer searches for an expression of the correct type that satisfies all refinement constraints. The synthesizer is chosen with the `-s` / `--synthesizer` flag:

```
uv run python -m aeon --budget 30 -s gp my_program.ae
```

The `--budget` flag sets the time limit in seconds (default: 60).

---

## Available Synthesizers

### `gp` — Genetic Programming *(default)*

Evolves a population of candidate programs using genetic programming, implemented via [GeneticEngine](https://github.com/alcides/GeneticEngine). Candidate programs are represented as syntax trees drawn from a grammar derived from the typing context. Selection, crossover, and mutation operators drive the search towards better fitness scores as defined by the synthesis decorators (`@minimize`, `@maximize`, etc.).

Best suited for problems with a rich fitness landscape and sufficient budget.

---

### `random_search` — Random Search

Randomly samples programs from the grammar at each step and validates them against the target type and refinements. Simple but effective as a baseline or for problems where the search space is small.

---

### `enumerative` — Enumerative Search

Systematically enumerates all programs up to increasing size bounds (iterative deepening). Guaranteed to find a solution if one exists within the grammar, provided the budget allows. Works well for small, tightly-constrained holes.

---

### `hc` — Hill Climbing

A local search strategy that starts from a random candidate and repeatedly mutates it, keeping improvements. Faster per iteration than full genetic programming but more prone to local optima.

---

### `1p1` — (1+1) Evolution Strategy

A minimal evolutionary strategy that maintains a single candidate, mutates it, and accepts the child if it is at least as good as the parent. Lightweight and surprisingly competitive on simple problems.

---

### `synquid` — Type-Directed Synthesis

This backend implements a **Synquid-style** enumerator: type-directed decomposition, **Q**-aware conditional guards (same finite qualifier set as Horn predicate abstraction), and search ordering heuristics.

**Search.** Default ``synquid_search: "size_merge"`` uses a **lazy min-heap** over synthesis levels (``term_size``, then shallower ``level``) via ``aeon.synthesis.modules.synquid.search.iter_candidates_size_then_level``. ``synquid_search: "iterative_deepening"`` restores strict “exhaust level *L* before *L+1*”. **Within** each level, candidates are sorted by ``term_size``. Tunables: ``synquid_max_level``, ``synquid_seed_levels``, ``synquid_max_candidates`` (hard cap on candidates tried per hole, both search modes); optional ``synquid_typecheck_candidate_first`` runs ``check_type`` on the candidate in the **hole** context before full-program validation.

**Enumeration.** Level 0 supports **Bool**, **Int**, **Float**, **String**, **Unit** (small fixed literal sets where applicable), **variables** matching the goal, and **type variables** satisfied from the typing context. **Arrow** goals at level 0 only enumerate matching **functions in scope** (no ill-scoped literal fall-through). At level ≥ 1 the enumerator emits **λ-abstractions** (``Abstraction``), optionally **annotated** when the goal is a **refinement over an arrow**, plus applications from the typing context. ``if`` branches try **quaternary**, **ternary**, **binary**, then **unary** relational guards built from **Q**, then plain boolean enumeration. Function applications are **pruned** when the callee’s result type does not match the goal (spine decomposition); refined argument types are preserved on the spine. ``aeon.synthesis.modules.synquid.modular`` exposes ``application_subgoal_types``, ``check_hole_term``, ``qualifier_atoms``, and **modular VCs** via ``build_modular_vc`` / ``ModularVC`` (re-exported from ``aeon.typechecking.partial_vc``); ``aeon.synthesis.modules.synquid.build`` re-exports the same surface. A **modular VC** is the ``Constraint`` from ``check`` before entailment, so callers can inspect it, pass a custom **Q** to ``solve``, or use ``explain_failures`` — distinct from a single ``check_type`` boolean.

**Fitness.** If the hole has **no** ``goals`` metadata, the first fully valid candidate is returned.

**Not in scope (vs the PLDI Synquid paper or ideal liquid tooling):** **MUSFIX-style** weakest-guard abduction (only bounded ``&&``-products over **Q**); **no** core-level ``match`` / ``fix`` (those live in sugar + elaboration); **Horn** lifting still **skips** polymorphic and refinement-polymorphic value binders (see comments in ``aeon/typechecking/entailment.py``). Modular VCs still rely on ``check`` internally, which calls ``check_type`` in a few places (e.g. ``if`` conditions) rather than returning those as nested VC objects. For further background on **Q** and refinement Horn encodings, see Jhala & Vazou, [Refinement Types: A Tutorial](https://arxiv.org/abs/2010.07763).

---

### `smt` — SMT-Guided Synthesis

Constructs a candidate expression top-down using the typing context:

- For **SMT base types** (`Int`, `Bool`, `Float`), it creates z3 placeholder variables and collects all active refinement constraints.
- For **non-SMT types**, it searches the context for constructor functions that return the target type and recursively synthesises their arguments.

Once the term structure is fixed, all constraints are discharged in a single z3 call. If satisfiable, the placeholders are replaced with the concrete values from the model and the result is validated.

Best suited for problems whose solution is primarily determined by arithmetic or boolean constraints on integers and floats — for example, finding a concrete value satisfying a chain of liquid-type inequalities.

Configurable option: `max_depth` (default 5) controls how deeply the synthesizer recurses when building non-SMT subterms.

---

### `decision_tree` — Decision Tree Regressor

Fits a scikit-learn `DecisionTreeRegressor` to training data provided via the `@csv_data` or `@csv_file` decorators, then converts the resulting tree into a nested `if-then-else` Aeon term. This synthesizer is **data-driven**: it learns a piecewise-constant function from examples rather than searching a grammar.

Useful for regression problems where input–output pairs are available and a readable, interpretable result is desired.

---

### `llm` — Large Language Model (Ollama)

Uses a locally running [Ollama](https://ollama.com/) instance to generate candidate expressions. The model (`qwen2.5:32b` by default) is prompted with a description of the synthesis problem, including the target type and any `@prompt("description")` decorator. Generated expressions are parsed, type-checked, and validated in a loop until the budget expires or a valid candidate is found.

Requires Ollama to be running locally. Use the `@prompt` decorator to provide a natural-language description of the desired behaviour.

---

## Choosing a Synthesizer

| Synthesizer     | Strategy         | Best for |
| --------------- | ---------------- | -------- |
| `gp`            | Evolutionary     | Complex expressions, multi-objective problems |
| `random_search` | Random sampling  | Baselines, small search spaces |
| `enumerative`   | Size-ordered enumeration | Small holes, tight type constraints |
| `hc`            | Local search     | Single-objective, unimodal problems |
| `1p1`           | Minimal evolution | Simple problems, fast iteration |
| `synquid`       | Type-directed enumeration | Type-rich problems, correctness-only goals |
| `smt`           | SMT solving      | Arithmetic / boolean constraints on base types |
| `decision_tree` | Data-driven      | Regression from input–output examples |
| `llm`           | LLM generation   | Problems that are easy to describe in natural language |
