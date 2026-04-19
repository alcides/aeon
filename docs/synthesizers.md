# Synthesizers

Aeon supports automatic synthesis of program holes (`?hole`). When a hole is present, a synthesizer searches for an expression of the correct type that satisfies all refinement constraints. The synthesizer is chosen with the `-s` / `--synthesizer` flag:

```
uv run python -m aeon --budget 30 -s gp my_program.ae
```

The `--budget` flag sets the time limit in seconds (default: 60).

---

## Available Synthesizers

### `tdsyn` — Type-Directed Synthesis *(default)*

Builds partial ASTs using backward and forward rules (functions whose return type matches the goal, or functions that consume variables in scope), SMT-based subtyping, and Z3 literal solving for base-type holes with refinements. Uses a worklist search (BFS in `enumerative` mode). Does **not** use GeneticEngine.

Use `tdsyn_random` for the same pipeline with random queue ordering instead of BFS.

---

### `gp` — Genetic Programming

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

Enumerates candidates by increasing size, prunes function applications when the goal return type is incompatible with the callee’s result (spine decomposition), and **prioritises `if` guards** built from **qualifier atoms** `Q` extracted from the typing context (the same finite `Q` used by the Horn solver for predicate abstraction; see Jhala & Vazou, [Refinement Types: A Tutorial](https://arxiv.org/abs/2010.07763)). Remaining search is still bounded enumerative; full Synquid-style round-trip checking and abduction are incremental goals.

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
| `tdsyn`         | Type-directed + SMT | Polymorphic and refinement-heavy holes; default CLI |
| `tdsyn_random`  | Type-directed + SMT (random order) | Same as `tdsyn`, different exploration |
| `gp`            | Evolutionary     | Complex expressions, multi-objective problems |
| `random_search` | Random sampling  | Baselines, small search spaces |
| `enumerative`   | Size-ordered enumeration | Small holes, tight type constraints |
| `hc`            | Local search     | Single-objective, unimodal problems |
| `1p1`           | Minimal evolution | Simple problems, fast iteration |
| `synquid`       | Type-directed enumeration | Type-rich problems, correctness-only goals |
| `smt`           | SMT solving      | Arithmetic / boolean constraints on base types |
| `decision_tree` | Data-driven      | Regression from input–output examples |
| `llm`           | LLM generation   | Problems that are easy to describe in natural language |
