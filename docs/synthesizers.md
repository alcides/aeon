# Synthesizers

Aeon supports automatic synthesis of program holes (`?hole`). When a hole is present, a synthesizer searches for an expression of the correct type that satisfies all refinement constraints. The synthesizer is chosen with the `-s` / `--synthesizer` flag:

```
uv run python -m aeon --budget 30 -s tdsyn_enumerative my_program.ae
```

The `--budget` flag sets the time limit in seconds (default: 60). The default synthesizer is **`tdsyn_enumerative`** (type-directed BFS); pass `-s gp` (or another id) to override.

---

## Available Synthesizers

### `gp` — Genetic Programming

Native genetic programming with a **linear genome**: each individual is a sequence of integer codons that select among Aeon's grammar expansions when mapped to a core term. There is no fixed max depth — choice budgets grow with the generation index and mutation can lengthen genomes, so trees deepen as evolution advances.

Population size is chosen from a timing probe of the first ten random individuals so that initial evaluation uses at most 10% of the wall-clock budget. Crossover rate and mutation rate are sampled randomly each run; tournament size, novelty rate and related operator knobs are re-sampled every generation. Elitism keeps the best 5% of the population. Fitness comes from the synthesis decorators (`@minimize_*`, `@maximize_*`, `@property`, …). When objectives are present the shared Pareto driver returns a random non-dominated candidate; otherwise the first well-typed term wins. No GeneticEngine dependency.

Best suited for problems with a rich fitness landscape and sufficient budget.

---

### `random_search` — Random Search

Native random walks over Aeon's core term grammar (the same backward and forward actions as `enumerative`). Each sample expands holes at random until a complete term is produced (or the depth bound is hit); the shared driver rejects those that fail typechecking, evaluates the rest, and keeps a Pareto front — returning a random non-dominated candidate when objectives are present, or the first well-typed term otherwise. No GeneticEngine dependency. Simple but effective as a baseline or for problems where the search space is small.

---

### `enumerative` — Enumerative Search

Native breadth-first enumeration over Aeon's core term grammar (backward and forward actions, plus SMT completion of refinement-constrained leaves). A generator yields complete terms; the driver rejects those that fail typechecking, evaluates the rest, and keeps a Pareto front — returning a random non-dominated candidate when objectives are present, or the first well-typed term otherwise. No GeneticEngine dependency. Works well for small, tightly-constrained holes.

---

### `rl_mcts` — Reinforcement-Learning Guided Grammar Tree Search

An Aeon adaptation of Parsert and Polgreen's [Reinforcement Learning and
Data-Generation for Syntax-Guided Synthesis](https://arxiv.org/abs/2307.09564),
sections 3–4. Search expands the **leftmost** typed hole, uses policy-weighted
UCT and value-guided backpropagation, and commits to the most-visited child at
each big step. Complete programs must pass the normal whole-program verifier;
predictions never establish correctness and no axioms are introduced.

Without a checkpoint it uses the paper's baseline: policy 1 and value
`0.95 ** remaining_holes`. Defaults follow the reported search parameters:
30 big steps, 6500 rollouts, decay `0.98 ** big_step`. Additional safety limits
are 100,000 nodes and eight recursive grammar expansions. These finite limits
make search incomplete; timeout is not evidence that no solution exists.

```bash
python -m aeon -s rl_mcts --budget 10 examples/synthesis/rl_mcts.ae
```

Learned guidance is optional and requires `pip install 'AeonLang[synthesis-rl]'`.
Set `AEON_RL_MCTS_MODEL=/path/to/checkpoint` to load it. Checkpoints contain
XGBoost policy/value models and a versioned feature manifest, not executable
Python pickles. Only load model files from trusted sources.

Training uses hashed symbols and parent/child term walks, with hash base 4093.
Value labels are `0.9 ** distance_to_solution` on successful paths and zero on
visited states of failed searches. Policy labels are child visits divided by
all sibling visits on successful paths. XGBoost tree depths are 20/25 for
value/policy. Training iteratively reruns problems and retains replay from the
last four iterations. Inference never updates models.

To train on Aeon, supply files with exactly one independent refinement hole:

```bash
python -m aeon.synthesis.modules.rl_mcts train-aeon train1.ae train2.ae \
  --output /tmp/aeon-model --iterations 2 --budget 10
AEON_RL_MCTS_MODEL=/tmp/aeon-model python -m aeon -s rl_mcts held-out.ae
```

The data-generation tool instead starts from **universally valid** quantifier-free
Int/Bool SMT formulas (satisfiability alone is insufficient). Anti-unification
preserves repeated disagreement pairs, lifts source variables into parameters,
and replaces selected, non-overlapping Int subterms with synthesis calls. It
checks the resulting generalizer as a witness, but never gives it to search.
The grammar includes constants from the source, addition/subtraction, constant
multiplication/division/modulo, comparisons, Boolean operators, and conditionals.
Nonlinear generalizers, quantifiers, arbitrary uninterpreted functions, other
sorts, and unknown solver answers are rejected. Automatic selection prefers
large same-head subterms; it does **not** reproduce the paper's corpus filtering
or published dataset.

```bash
python -m aeon.synthesis.modules.rl_mcts generate \
  examples/synthesis/rl_mcts_training.smt2 --output /tmp/aeon-rl-data
python -m aeon.synthesis.modules.rl_mcts train \
  examples/synthesis/rl_mcts_training.smt2 --output /tmp/aeon-smt-model \
  --iterations 2 --limit 2 --budget 10
```

Both adapters share the same search/replay implementation, but SMT syntax and
Aeon compiler ASTs have different feature vocabularies. Train on Aeon problems
for Aeon inference; a generated-SMT checkpoint is not a demonstrated transfer
model. Keep training and held-out tasks separate. Training fails explicitly
if no iteration finds a successful policy path.

Unlike the numerical search backends, `rl_mcts` currently supports correctness
specifications only and rejects objective decorators (including property-fitness
objectives). Its grammar comes from Aeon's shared backward/forward actions, not
an imported arbitrary SyGuS grammar. Constants and supported polymorphic/ADT
components inherit that grammar's limitations. Calls into the compiler/verifier
are synchronous, so a final in-flight check can overrun the search time budget.
This implementation is not a reproduction of the paper's performance results;
no pretrained model or published 1901-task dataset is bundled.

---

### `structure_guided` — Structure-Guided Recursive Synthesis

Synthesizes recursive list-producing functions from constructor-literal
`@example` pairs using **size recurrences, partial-structure pruning, and local
element synthesis**. Inspired by Lin and Morihata's [Recursive function synthesis
based on structural relationships](https://jssst.or.jp/files/user/taikai/2025/papers/5a-1-R.pdf)
and [Structure-Element Separation (GPCE 2026)](https://2026.ecoop.org/details/ecoop-gpce-2026/6/Synthesizing-Recursive-Functional-Programs-via-Structure-Element-Separation).
This is a bounded adaptation to Aeon's constructor representation, not a
reproduction of the full published synthesizer or benchmark results.

```bash
python -m aeon -s structure_guided --budget 10 examples/synthesis/structure_guided/paired_map.ae
python -m aeon -s structure_guided --budget 10 examples/synthesis/structure_guided/tree_inorder.ae
```

The target must have one value parameter, a body hole, `@allow_recursion`, and
literal input/output examples. It may accept a list or binary-tree datatype;
the result is a list of integers. Datatypes must be registered inductives with
exactly two constructors: one nullary base and one recursive constructor with
one or two immediate recursive fields and one or two Int fields. Outputs need
exactly one recursive field and one Int field. Constructor names, declaration
order and field order are discovered from the typing context, rather than
hardcoded. Parametric datatypes instantiated at Int are supported. Explicit
type applications such as `List.nil{Int}` may be needed in examples when the
frontend cannot infer a nullary constructor's type arguments.

**Search.** First infer every bounded recurrence consistent with the examples:

```text
length(f empty) = d
length(f node)  = c + sum(a_i * length(f child_i))
```

For lists there is one child; for binary trees there are two. Sizes are computed
by recursively expanding the input structure, not by assuming recursive outputs
have the input children's sizes. Ambiguous examples retain all fitting models.

The output-constructor/append grammar normalizes to a word whose tokens are
individual element holes or calls on immediate input children. Top-down prefix
expansion tracks constructor and call counts. Prefixes incompatible with every
inferred model are pruned before element expressions are enumerated. A stutter
task requiring two new elements per recursive step therefore rejects a complete
one-constructor skeleton while its element hole is still open. Constructor
order and the order of recursive calls remain search choices, supporting such
tasks as reverse, repeated maps and tree traversal.

Next, symbolic execution unrolls each candidate skeleton into **diamond** atoms
carrying a hole identity and its local integer inputs. Positional alignment with
expected outputs produces small PBE tasks for each hole. Conflicting observations
reject a skeleton immediately. Each task is solved by size-ordered enumeration
of local Int fields, literals and `+`, `-`, `*`, with observational equivalence
on that task's examples. No reference stutter, reverse, map or traversal program
is supplied to search.

The resulting core term uses actual datatype constructors, recursors and
immediate-child self-calls. When concatenation is needed, a local recursive
append is generated from the output datatype and checked with the rest of the
candidate. No arbitrary library function is assumed to implement append.
Acceptance requires **both** the normal whole-program validator and execution
against every supplied I/O example. The runtime probe ties the recursive self
name to the candidate, so it cannot accidentally test the placeholder body.

**Bounds.** Each `Config` field can be set with an integer environment variable
`AEON_STRUCTURE_<FIELD_NAME>`, or through
`StructureGuidedSynthesizer(Config(...))` (import `Config` from
`aeon.synthesis.modules.structure_guided.search`). Defaults are:

- `MAX_CALLS=2`: total child-call occurrences in the recursive word.
- `MAX_ADDED=3`, `MAX_BASE=1`: element constructors per step and in the base.
- `MAX_ELEMENT_SIZE=7`: maximum AST node count per integer element expression.
- `MAX_VALUES=5000`, `MAX_SKELETONS=10000`: local value and prefix search caps.
- `MAX_NODES=128`, `MAX_DEPTH=16`: structural example / symbolic output bounds.

The wall-clock budget covers recurrence inference, structural and element search,
and runtime example checks. Compiler validation and individual synchronous
evaluation calls can overrun the budget; no new process-based timeout is added.
Search counters are available as `backend.stats`, including pruned prefixes,
alignment/local-task counts and candidate validation/runtime rejections.

**Limits and guarantees.** This backend learns from examples; inferred size
relationships do not prove a universal functional specification. Any declared
refinement still has to pass Aeon's ordinary verifier. Fixed-recurrence search
does not cover value-dependent filtering, arbitrary recursion, accumulator
parameters, tree-valued results, nested/mutual datatypes, opaque library calls,
Boolean element computations, extra optimization goals or relational examples.
Unsupported goals are reported explicitly. Search bounds, finite literal and
element grammars, and observational merging make search incomplete: exhaustion
is not evidence that no implementation exists. Like other per-hole backends,
this backend does not jointly solve coupled holes.

---

### `synquid` — Type-Directed Synthesis

This backend implements round-trip checking, incremental shape/refinement constraints, MUSFIX condition abduction, polymorphic function and fixpoint introduction, and datatype match synthesis. See [the implementation and validation notes](synquid-round-trip.md) for supported fragments, bounds, and differences from PLDI 2016 Synquid.

**Search.** Default `synquid_search: "paper"` streams rule-directed candidates at increasing application depth, with independent `synquid_match_depth` (default 2). `"size_merge"` merges candidates by AST size and depth; `"iterative_deepening"` exhausts each sorted level. Tunables remain `synquid_max_level`, `synquid_seed_levels`, `synquid_max_candidates`, and `synquid_typecheck_candidate_first`. The time budget also applies during candidate construction. Each level yields at most 4,000 candidates. Term memoization is disabled because `(context, level, goal)` does not identify the pending constraint state.

**Applications.** The expected result constrains liquid polymorphic instantiations before arguments are chosen. Independent result obligations are checked immediately; dependent obligations remain pending. Selected arguments contribute their inferred refinements and existential witnesses. Consistency checks ask whether remaining arguments and the result can jointly satisfy their contracts, including datatype measures and branch assumptions. Only proved failures or exhaustion of a finite qualifier space reject an alternative; SMT unknown/unsupported outcomes remain eligible for final verification. Higher-order arguments can be deferred until first-order arguments determine their types.

**Conditionals.** Search proposes a branch under an unknown path predicate, derives its verification conditions, and strengthens the predicate from `true` using MUSFIX-style minimal-subset enumeration. It retains incomparable solutions, removes semantically stronger guards, realizes a Boolean expression, and builds the other branch under the guard's negation. The bounded qualifier-conjunction enumerator remains a fallback when abduction cannot handle the obligation or its vocabulary is insufficient.

**Validation and observability.** Every accepted candidate still passes the supplied whole-program validator, including termination checks. With no fitness goals, the first valid candidate is returned. `SynquidSynthesizer.stats` records generated arguments, partial rejections, full validations, abduction proposals/guards, fallback guards, solver queries, and explicit solver outcomes. `modular.py` continues to expose the compatibility decomposition API and `ModularVC`.

---

### `polynomial` — Polynomial Certificate Synthesis

Synthesizes bounded-degree polynomial expressions using algebraic certificates,
inspired by Goharshady et al., [Template-based Program Synthesis using
Stellensätze](https://arxiv.org/abs/2209.03602). It fills all program holes jointly
using the compiler's shared verification conditions, including when there is
only one hole. Refinement contracts, surrounding code, `@example` relations,
and `@property` functions contribute logical obligations; properties are checked
universally by the certificate encoding, rather than only on their runtime corpus.

```bash
python -m aeon -s polynomial --budget 10 examples/synthesis/polynomial.ae
python -m aeon -s polynomial --budget 10 examples/synthesis/polynomial_sketch.ae
```

Each numeric hole receives a polynomial template over its lexical inputs with
unknown coefficients. For example, an `Int -> Int` hole at degree two searches
`c0 + c1*x + c2*x*x`. Int holes use integer coefficients; Float holes use real
coefficients. Explicit coefficient holes can also fill a programmer-supplied
larger sketch, as the second example demonstrates.

For an obligation `g_i >= 0, h_j = 0 => p >= 0`, the backend constructs:

```text
p = sum(lambda_alpha * product(g_i ** alpha_i))
    + sigma_0 + sum(sigma_i * g_i) + sum(q_j * h_j)
```

The `lambda` coefficients are nonnegative (Handelman products); every `sigma`
is a sum of polynomial squares (Putinar-style multipliers); the `q` polynomials
are unrestricted equality multipliers. Coefficient matching makes this a purely
existential SMT problem: universal input variables disappear from the synthesis
solver. Linear cases include Farkas-style certificates. Equalities are proved
in both directions; strict conclusions additionally require a positive constant
margin. The solver returns a feasible program, not an objective optimum. The
complete result must pass Aeon's ordinary whole-program validator before fitness
evaluation or publication to the UI.

Configure the finite search space through environment variables:

- `AEON_POLYNOMIAL_DEGREE` (default `2`): total degree of each hole template.
- `AEON_POLYNOMIAL_CERTIFICATE_DEGREE` (default `2`): maximum number of factors
  in a Handelman product, and total degree of each equality multiplier.
- `AEON_POLYNOMIAL_SOS_DEGREE` (default `1`): degree of each polynomial before
  squaring. Set to `0` to disable the SOS terms and use Handelman/equality
  certificates alone.

The Python API accepts `PolynomialConfig`, including limits of 4096 monomials /
product expansion pairs, 10,000 unknown coefficients, and 64 premise branches.
The budget covers template construction, certificate expansion and solving;
the final synchronous compiler validation / objective evaluation is additional.

**Supported subset and guarantees.** Numeric holes need homogeneous Int or
Float parameters and results. Expressions support constants, variables, hole
calls, addition, subtraction and multiplication. Conclusions are conjunctions
of numeric equalities/inequalities; premises also allow disjunction and negation.
Boolean compiler value binders are eliminated when they are definitions; arbitrary
Boolean inputs and Boolean-valued holes are unsupported. Integer division,
modulo, division in source specifications, conditional arithmetic, ADTs and opaque
native calls are rejected explicitly. A positive SOS degree uses a full square
factorization of the bounded monomial Gram matrix, rather than only diagonal
squares; no external SDP solver is needed.

Certificates prove obligations over mathematical reals. Int variables are
conservatively relaxed to reals while program coefficients remain integers;
strict premise inequalities are conservatively closed. These choices are sound
but can miss programs valid only on discrete or open domains. Float follows
Aeon's existing real-arithmetic refinement semantics, not an IEEE-754 roundoff
guarantee. Rational program coefficients are emitted as ratios of exactly
representable integer-valued Float literals; irrational or excessively large
coefficients are rejected.

Failure means no certificate was found at these bounds, or the solver timed
out / returned unknown; it does not establish unrealizability. This is a bounded
Handelman/SOS backend, not the paper's full imperative-program frontend,
automatic loop-invariant synthesis, Real Nullstellensatz procedure, or its
semi-completeness theorem. The generated constraints can be higher than quadratic
when holes occur in assumptions or are composed; no general QP reduction or
published performance result is claimed.

---

### `noisy` — Regularized Synthesis from Noisy Examples

Treat scalar I/O examples as soft observations while keeping refinement checking
mandatory. A bounded native generator and history-based sampler minimize
mismatch rate plus a configurable complexity penalty. See
[noisy-example synthesis](noisy-synthesis.md) for configuration, residual reports,
supported inputs, and reproducible adaptive/uniform/full-data comparisons.

### `smt` — SMT-Guided Synthesis

Constructs a candidate expression top-down using the typing context:

- For **SMT base types** (`Int`, `Bool`, `Float`), it creates z3 placeholder variables and collects all active refinement constraints.
- For **non-SMT types**, it searches the context for constructor functions that return the target type and recursively synthesises their arguments.

Once the term structure is fixed, all constraints are discharged in a single z3 call. If satisfiable, the placeholders are replaced with the concrete values from the model and the result is validated.

Best suited for problems whose solution is primarily determined by arithmetic or boolean constraints on integers and floats — for example, finding a concrete value satisfying a chain of liquid-type inequalities.

Configurable option: `max_depth` (default 5) controls how deeply the synthesizer recurses when building non-SMT subterms.

---

### `bustle` — Learning-Guided Bottom-Up Synthesis

Implements the core of [BUSTLE (ICLR 2021)](https://arxiv.org/abs/2007.14381): enumerate typed expressions bottom-up by weight, execute them on scalar or closed-constructor `@example` inputs, merge observationally equivalent output vectors, and use a trained property-signature MLP to adjust intermediate-expression weights. Predictions are batched; the paper's probability bins add penalties from 0 to 5. Inputs and constants remain at weight 1. An expression must match every example and pass Aeon's type validation before acceptance.

The bundled model was trained reproducibly on synthetic bottom-up searches. It uses NumPy when installed and otherwise standard-library inference, with no model downloads or PyTorch dependency. `AEON_BUSTLE_MODEL` selects a compatible JSON checkpoint. `-s bustle_baseline` explicitly disables learned guidance for comparison.

Supports one to three scalar or registered ADT inputs, scalar or ADT results, first-order in-scope components, and conditionals. ADT guidance uses constructor identity, depth, size, and subtree relations; merging uses full structural identity, including scalar field types. Concrete polymorphic ADT instantiations are supported. ADTs are bounded to depth 16 and 128 constructor nodes. This is an example-driven backend, not an optimizer for arbitrary fitness objectives; unsupported goals/types are reported explicitly. Search is bounded by adjusted weight 40, 20,000 distinct values, and the time budget. See [examples, training instructions, and differences from the paper](../examples/synthesis/bustle/README.md).

---

### `arborist` — Lifted Interpretation with Local Variables

Adapts the lifted interpretation algorithm from [Li et al., POPL 2024](https://arxiv.org/abs/2311.03705), Section 3 and Appendix A. A bounded typed grammar is stored as a packed tree language. Interpreting the enclosing Aeon sketch discovers reachable local bindings; specializing the grammar under each binding context constructs observational classes bottom-up while retaining all their alternatives. A subsequent call specializes the surviving language, allowing classes to split and ensuring that every fold iteration uses the same candidate body.

Select it with `python -m aeon --no-main --budget 10 -s arborist examples/synthesis/arborist/list_fold.ae`. It accepts literal Int/Bool or closed registered-constructor inputs, Int/Bool outputs, and one Int/Bool expression hole inside a supplied pure functional sketch. Supported surrounding Core forms include lambdas, applications, local bindings, conditionals, recursive functions, and compiler-generated constructors/eliminators (`match`). The supplied fold combinators are interpreted from their Aeon definitions; their accumulator contexts depend on candidate outputs. Generated expressions use lexical scalar variables, small constants, arithmetic, comparisons, Boolean operations, and conditionals. `list_fold.ae` preserves the paper's ambiguous `[1,2,4] → 7` example; `list_sum.ae` adds distinguishing examples.

The backend uses the program-level synthesis interface to observe the enclosing execution. Every extracted solution passes the usual whole-program type/refinement validator and the examples in Aeon's normal evaluator. Rejection of one example-equivalent representative does not discard its alternatives. Search observes the wall-clock budget, with default limits of three nested grammar operations, 100,000 packed states, one million interpreter steps, and 4096-bit integers. An in-flight compiler check or final runtime check can overrun the budget.

This implementation searches bodies in a fixed sketch, not arbitrary loop structures or the paper's web-automation language. Constructor inputs/intermediates are bounded to 128 total nodes and depth 32. ADT-valued holes/results, Float/String leaves, arbitrary native/effectful components, multiple holes, and optimization objectives are unsupported. Recognizing compiler-generated inductives does not enable general native execution in the lifted interpreter. Unlike `fta` and `bustle`, its equivalence classes account for execution-dependent local bindings; unlike `afta`, it uses exact concrete observations rather than abstraction refinement. See the [examples, invariants, restrictions, and compression experiment](../examples/synthesis/arborist/README.md).

---

### `decision_tree` — Decision Tree Regressor

Fits a scikit-learn `DecisionTreeRegressor` to training data provided via the `@csv_data` or `@csv_file` decorators, then converts the resulting tree into a nested `if-then-else` Aeon term. This synthesizer is **data-driven**: it learns a piecewise-constant function from examples rather than searching a grammar.

Useful for regression problems where input–output pairs are available and a readable, interpretable result is desired.

---

### `llm` — Large Language Model (Ollama)

Uses a locally running [Ollama](https://ollama.com/) instance to generate candidate expressions. The default model is `qwen2.5-coder:32b`; per-model backends are also available (e.g. `-s llm_qwen2.5-coder-14b`). The LSP menu lists each model by its Ollama tag. The model is prompted with a description of the synthesis problem, including the target type and any `@prompt("description")` decorator. Generated expressions are parsed, type-checked, and validated in a loop until the budget expires or a valid candidate is found.

Curated models for Apple Silicon with ≤64 GB RAM. Models are **pulled automatically** on first use (disable with `AEON_OLLAMA_AUTO_PULL=0`). Before synthesis, other loaded Ollama models are **unloaded from memory** to stay within `AEON_OLLAMA_MEMORY_BUDGET_GB` (default 56). After synthesis, the active model is released from RAM (disable with `AEON_OLLAMA_RELEASE_AFTER=0`).

| Synthesizer id | Ollama model | Approx. size (Q4) |
| -------------- | ------------ | ----------------- |
| `llm` / `llm_qwen2.5-coder-32b` | `qwen2.5-coder:32b` | ~20 GB |
| `llm_qwen2.5-coder-14b` | `qwen2.5-coder:14b` | ~9 GB |
| `llm_deepseek-coder-v2-16b` | `deepseek-coder-v2:16b` | ~10 GB |
| `llm_codellama-13b` | `codellama:13b` | ~8 GB |
| `llm_starcoder2-15b` | `starcoder2:15b` | ~9 GB |
| `llm_deepseek-coder-6.7b` | `deepseek-coder:6.7b` | ~4 GB |

Requires Ollama to be running locally. Use the `@prompt` decorator to provide a natural-language description of the desired behaviour.

---

### `tdsyn` / `tdsyn_enumerative` — Type-Directed Synthesis (BFS) *(default)*

Top-down, type-directed synthesizer that grows a partial AST by applying **backward** and **forward** actions to each open hole. Subtyping queries are discharged by an SMT solver, and when every remaining hole is a base-type leaf the synthesizer asks z3 to solve them all in one shot.

Search is breadth-first over partial ASTs (capped by a depth bound). When the worklist is exhausted, the search restarts with a shuffled expansion order so that subsequent iterations explore different term shapes until the budget runs out. If no optimization goals are present, the first valid term is returned; otherwise the best-scoring term across iterations wins.

---

### `tdsyn_random` — Type-Directed Synthesis (Random Walks)

Same expansion rules as `tdsyn`, but instead of a BFS worklist it performs independent random walks from the initial hole. Each walk repeatedly picks a random open hole and a random candidate expansion, falling back to SMT completion when only base-type leaves remain. Lighter than the BFS mode, useful when the term space is wide and shallow.

---

### `tdsyn_backward` — Backward Step (Combined)

Demonstrative single-step backend: applies the **backward** action exactly once to the hole. Candidates are derived from the hole's expected type (literals, variables and function applications whose result type matches, abstractions, if-then-else). Returns the first complete candidate that typechecks, or otherwise the first partial expansion with fresh `?<fun>_goal_<i>` subgoal holes, so the step can be applied again. No search is performed — use `tdsyn` for actual synthesis.

This is the union of the granular `backward_*` steps; use those to apply one backward construction at a time.

---

### `backward_abs` / `backward_lit` / `backward_close` / `backward_app` / `backward_if` — Backward Steps

Demonstrative single-step backends: each applies one slice of the backward action exactly once to the hole, so the constructions bundled in `tdsyn_backward` can be applied one by one:

| Backend | Candidates |
|---|---|
| `backward_abs` | `fun x -> ?body` for a function-typed goal, with `?body` typed by the codomain and `x` in scope (other steps auto-abstract function-typed goals, so this step makes that introduction explicit) |
| `backward_lit` | literals of the goal's base type (`Int`, `Bool`, `Float`) |
| `backward_close` | an in-scope variable whose type already proves the goal — the same candidates as `forward_close`, exposed under both directions' menus |
| `backward_app` | `f(?h1, ..., ?hn)` for each in-scope (possibly monomorphized) function whose return type matches the goal, leaving holes for the arguments |
| `backward_if` | `if ?c then ?t else ?e` with branches typed by the goal |

Each returns the first complete candidate that typechecks, or otherwise the first expansion with fresh `?<fun>_goal_<i>` subgoal holes, so steps can be chained. No search is performed — use `tdsyn` for actual synthesis.

---

### `forward_close` / `forward_let_*` — Forward Steps

Demonstrative single-step backends: each applies its forward action exactly once to the hole. `forward_close` closes the goal with a variable whose type already proves it. The `forward_let_*` tactics grow the scope with a `let v := <value> in ?goal` binding, reopening the goal with `v` in scope; each variant binds one term former as the value:

| Backend | Let value | Type of `v` |
|---|---|---|
| `forward_let_app` | forward application `f(x, ?...)` (in-scope function applied to an in-scope variable, result matching the goal) | the application's unrefined result type |
| `forward_let_if` | `if ?c then ?t else ?e` with branches typed by the goal | the goal type |
| `forward_let_tapp` | monomorphic instantiation of a polymorphic in-scope variable (operators insert as sections, e.g. `(=)`) | the instantiated type |
| `forward_let_abs` | `fun x -> ?body` with `?body` typed by the goal, for each built-in base domain | `(x:domain) -> goal` |
| `forward_let_tabs` | `Λa:B. ?body` with `?body` typed by the goal | `forall a:B, goal` |

Each returns the first complete candidate that typechecks, or otherwise the first expansion with fresh `?<fun>_goal_<i>` subgoal holes, so steps can be chained. No search is performed — use `tdsyn` for actual synthesis.

When a function has several holes (e.g. the subgoals a previous step inserted), the LSP Synthesize action targets exactly the hole it was invoked on and leaves the siblings open; on the CLI, synthesis fills the first hole of each function.

---

### `tactics` — Random Tactic Search

A Lean-style tactic synthesizer. The proof obligation (the hole's goal type in its typing context) is reduced step by step by repeatedly choosing a random open hole and a random tactic from:

- `apply?` — apply a function from context, leaving holes for its arguments
- `assumption` — close the hole with a matching binding from context
- `constructor` — apply an inductive-type constructor
- `inst` — instantiate a type or refinement parameter
- `choose_literal` — pick a base-type literal
- `by_cases` — split on a boolean
- `split` — split a conjunction in the goal

Each iteration starts a fresh walk (up to 20 tactic steps); walks that fail to close all holes are abandoned. When optimization goals are present, the best-scoring closed walk across the budget is returned.

---

### `lta` — Liquid Tree Automata

Component-based synthesis via Liquid Tree Automata (Algorithm 1 of the LTA paper). An automaton is seeded from the library functions in scope, the parameters of the goal type, and a minimal set of constants. It is then iteratively expanded by an explore-reduce-check loop:

1. **Transition** — one round of E-app expansion pairs every function state with every argument state.
2. **Prune** — drops states whose refinements are unsatisfiable.
3. **Similarity / Minimize** — collapses observationally equivalent states.
4. **Goal check** — Q-goal transitions try to connect candidate states to the goal type; a non-empty final state yields a candidate term.

Polymorphic library functions are kept as cyclic *template* states and finitely unrolled into monomorphic instantiations against a small type universe. The expansion is depth-bounded (default `max_depth = 4`).

---

## Choosing a Synthesizer

| Synthesizer     | Strategy         | Best for |
| --------------- | ---------------- | -------- |
| `gp`            | Native linear-genome GP | Complex expressions, multi-objective problems |
| `random_search` | Native random walks over the core grammar | Baselines, small search spaces |
| `enumerative`   | Native BFS over the core grammar | Small holes, tight type constraints |
| `rl_mcts`       | Policy/value-guided Monte-Carlo grammar search | Refinement-only synthesis, learned search experiments |
| `synquid`       | Type-directed enumeration | Type-rich problems, correctness-only goals |
| `smt`           | SMT solving      | Arithmetic / boolean constraints on base types |
| `decision_tree` | Data-driven      | Regression from input–output examples |
| `noisy` | Regularized native search with adaptive sampling | Scalar examples with outliers or contradictory observations |
| `llm`           | LLM generation   | Problems that are easy to describe in natural language |
| `tdsyn` / `tdsyn_enumerative` | Type-directed BFS with SMT leaves | Tightly-typed holes where leaves reduce to arithmetic |
| `tdsyn_random` | Type-directed random walks with SMT leaves | Wider, shallower term spaces than `tdsyn` |
| `tdsyn_backward` | Single combined backward step (no search) | Demonstrating how the backward action decomposes a goal |
| `backward_abs` / `backward_lit` / `backward_close` / `backward_app` / `backward_if` | Single backward step (no search) | Applying one backward construction at a time |
| `forward_close` | Single forward step (no search) | Closing a goal with a variable already in scope |
| `forward_let_app` / `forward_let_if` / `forward_let_tapp` / `forward_let_abs` / `forward_let_tabs` | Single forward step (no search) | Demonstrating how forward reasoning grows the scope with `let` bindings |
| `tactics`       | Random tactic walks (Lean-style) | Goals whose proof decomposes into tactic steps |
| `lta`           | Component-based via Liquid Tree Automata | Reusing a library of refined functions to assemble a term |

---

## Benchmarks

The [Hakank common CP starter suite](../examples/synthesis/hakank/README.md)
contains 25 standalone, finite constraint and optimization models drawn from
the archived catalogue. Run these with `-s ortools`; decisions remain numeric
holes, with constraints expressed through comparisons, Boolean combinations,
and numeric conditionals. The suite includes pinned provenance, explicit
instance sizes, objective targets, regeneration tooling, and independent
checks of synthesized assignments.

For the catalogue of synthesis and verification benchmarks bundled with Aeon —
where they live, how many there are, and how to run them — see
[benchmarks.md](benchmarks.md).
