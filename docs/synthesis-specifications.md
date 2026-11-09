# Specification support across synthesizers

This audit follows [How to express intent in aeon](https://wiki.alcidesfonseca.com/blog/how-to-express-intent-in-aeon)
(November 3, 2026): types, liquid refinements, documentation, examples, CSV data,
optimization, properties, and resource use. It also covers `@minimize_size`.
The table includes every registered backend family on `master`, including
AMaze, bounded Boolean synthesis, ReGuS, and constrained LLM decoding.
Aliases with the same implementation share a row.

All complete candidates must satisfy their types and refinements. A backend's
existing grammar, type, arity and budget limits still apply: accepting a
specification does not mean its search can express or find every solution.
`@doc` guides **LLM generation only**. Other algorithms accept it as documentation;
there is no sound general conversion from natural language to assertions.

## Semantics

* **Fitness:** errors guide search and participate in tradeoffs. A returned
  candidate can fail examples or properties when these are soft objectives.
* **Check:** examples or the fixed generated property corpus must pass before
  acceptance. Passing generated tests does not prove a property universally.
* **I/O:** exact observations guide example-driven generation; extra assertions
  still use the shared validator.
* **Pareto:** retain nondominated explored candidates, respecting each objective's
  minimize/maximize direction. External enumeration ranks candidates but does
  not necessarily guide their generation.
* **Scalar:** rank by the backend's oriented scalarization, not a full Pareto
  archive. This is SyMetric's existing metric-search contract.

Both `@csv_data` and `@csv_file` use the declared argument and result types:
`Int`, `Float`, `Bool`, and `String`. Numeric outputs produce squared-error
fitness; Boolean/string outputs produce mismatch counts. Malformed cells and
unsupported schemas fail explicitly. Satisfaction backends require an exact
fit; regression and noisy learners retain approximate fitting. Constructor CSV
schemas are not inferred. Concrete constructor examples can still come from
`@example` or functional properties.

## Backend matrix

“Objectives” covers scalar min/max and multiple objectives, including mixed
directions. “Resources” covers CPU time and energy. Size and resources use the
same fitness infrastructure, subject to the stated search limits.

| Synthesizer IDs | Examples and CSV | Properties | Objectives | Size / resources | Meaningful limits |
| --- | --- | --- | --- | --- | --- |
| `tdsyn`, `tdsyn_enumerative`, `tdsyn_random`, `tdsyn_backward` | Fitness | Fitness | Pareto | Yes | Type-directed grammar and budget. |
| `backward_*`, `forward_*` | Check complete results | Check complete results | Unsupported | Unsupported | Interactive single expansion steps may leave subgoals. |
| `synquid` | Fitness | Fitness | Pareto | Yes | Refinement-directed grammar; zero is not assumed optimal for arbitrary goals. |
| `tactics` | Fitness | Fitness | Pareto | Yes | Complete tactic walks; fixed explicit `by` scripts only validate specifications. |
| `enumerative` | Fitness | Fitness | Pareto | Yes | Native term grammar. |
| `random_search` | Fitness | Fitness | Pareto, including joint holes | Yes | Native term grammar. |
| `gp` | Fitness | Fitness | Pareto, including joint holes | Yes | Native term grammar and sampled genomes. |
| `rl_mcts` | Check | Check | External Pareto | Yes | Feasibility currently supplies the positive search reward. |
| `decision_tree` | Numeric regression + fitness | Fitness; functional equalities can supply labels | Pareto over fitted trees | Yes | Numeric inputs/results; candidate trees of increasing depth, constant models for nullary data. |
| `noisy` | Soft scalar observations, including both CSV forms | Check | Pareto with built-in regularized risk | Yes | Bounded scalar learner; only fully scored candidates enter the front. |
| `contata` | Unary Int/Bool/List I/O + check; typed CSV where scalar | Check; equalities can supply labels | External Pareto for a single function | Yes for a single function | Mutual recursive groups retain their joint checking oracle, but reject numeric optimization. |
| `structure_guided` | Recursive-constructor I/O + check; CSV signature does not fit | Check; constructor equalities can supply labels | External Pareto | Yes | Recursive input/output ADTs; bounded recurrence extraction. |
| `bustle`, `bustle_baseline` | Scalar/constructor I/O + check; Int/Bool/String CSV | Check; equalities can supply labels | External Pareto | Yes | Float is outside its grammar. |
| `fta` | Numeric I/O + general checks; exact-fit numeric CSV | Check | External Pareto | Yes | Objective mode retains observationally equal alternatives. |
| `afta` | I/O + general checks; exact-fit CSV in supported sorts | Check | External Pareto | Yes | Objective mode retains observationally equal alternatives. |
| `cata` | Check; exact-fit CSV within its grammar | Check | External Pareto | Yes | Constraint-annotated grammar. |
| `lta` | Check; exact-fit CSV within its grammar | Check | External Pareto | Yes | Bounded liquid-automaton extraction. |
| `arborist` | Int/Bool-result I/O in a sketch + check; typed CSV | Check; equalities can supply labels | External Pareto | Yes | Existing lifted-interpreter types and sketches; no Float leaves. |
| `symetric`, `xfta` | Fitness | Fitness | Scalar | Yes | Requires a usable output metric or `@cluster` feature space. |
| `smt` | Single: fitness; joint: logical/check | Single: fitness; joint: logical/check | Single: Pareto; joint: external Pareto | Yes | Supported solver sorts and bounded candidate templates. |
| `sygus` | Check; joint examples also logical | Check; joint properties also logical | External Pareto | Yes | cvc5 grammar/sort support; incremental solution enumeration. |
| `polynomial` | Logical examples; exact-fit CSV check | Logical + check | External Pareto | Yes | Arithmetic polynomial fragment and coefficient/certificate bounds. |
| `ortools`, `ortools_int`, `cpsat` | Hard examples; soft CSV regression | Check and continue to next assignment | Pareto over blocked assignments | Yes | Bounded numeric/Bool holes, fixed-length arrays and lists; fixed-point Float representation. |
| `boolean_bounded` | Logical examples; exact-fit Bool CSV check | Logical Boolean obligations + check | External Pareto over finite CNF selectors | Yes | First-order Boolean functions and declared CNF bound. |
| `amaze` | Fitness; typed Int/Bool CSV | Fitness | Pareto | Yes | Learned Int/Bool grammar. |
| `regus` | Fitness; CSV does not fit controller signature | Fitness | Pareto | Yes | `ControlProgram` and the `@cluster` execution-observation protocol. |
| All regular `llm*` IDs | Fitness and prompt hints | Fitness and prompt hints | Pareto among generated terms | Yes | Provider/model generation quality; ordinary compiler validation. |
| `llm_type_constrained` | Fitness and prompt hints | Fitness and prompt hints | Pareto among decoded terms | Yes | Monomorphic scalar types/arrows; one hole, no ADTs/recursion/linear types. |

The single-step IDs are `backward_abs`, `backward_lit`, `backward_close`,
`backward_app`, `backward_if`, `forward_close`, `forward_let_app`,
`forward_let_if`, `forward_let_tapp`, `forward_let_abs`, and `forward_let_tabs`.
Regular LLM IDs are `llm`, `llm_openai`, `llm_qwen2.5-coder-32b`,
`llm_qwen2.5-coder-14b`, `llm_deepseek-coder-v2-16b`, `llm_codellama-13b`,
`llm_starcoder2-15b`, and `llm_deepseek-coder-6.7b`.

## Shared adapters

`Goal.kind` distinguishes checkable error counts from general objectives.
`specifications.py` installs timed acceptance checks for satisfaction backends;
`program_specifications.py` shares whole-program substitution, completeness,
type/bounded-contract checks, fixed property corpora and objective evaluation
across CP-SAT, noisy search, and final program-backend acceptance.

`example_adapters.py` merges typed CSV and derived observations without
modifying source metadata. A functional property such as `f x = reference x`
provides exact labels for its generated inputs. The same bounded evaluator
handles nonliteral examples such as `f (1 + 1) = 3`. It evaluates only independent
expressions, retains conflicting observations, and leaves the original assertions
in validation. Equalities can be reversed or unconditionally conjoined.
Inequalities, implications and relationships between multiple calls do not become
invented labels. When a learner still needs data, uniquely determined refinement
outputs provide sampled examples through `refinement_examples.py`.

A minimized squared error (or maximized negative squared error) can supply
training labels while retaining the original objective. An arbitrary
`minimize(f x - c)` cannot soundly be converted into `f x = c`.

`CandidateArchive` keeps feasible candidate streams running for optimization.
Z3 blocks function interpretations, cvc5 requests successive synthesis solutions,
polynomial synthesis blocks program coefficients, CP-SAT blocks whole assignments,
and bounded Boolean synthesis blocks selector models. Runtime failure rejects a
candidate; exhaustion preserves a valid incumbent. PBE optimization retains
syntactically different subterms even if they agree on examples, since their
objectives can differ.

Both LLM adapters share one specification prompt formatter, including objective
directions, generated goal/property definitions, CSV rows, resource goals and
`@doc`. Prompts guide generation; they do not replace evaluation or typechecking.

## Returned fronts and validation

Pareto-capable adapters expose `backend.pareto_front` as
`[(objective_values, core_term), ...]`, and report it through
`SynthesisUI.register_front`. Joint entries contain a `JointCandidate` holding
all hole replacements. The existing synthesis API returns one seeded selection;
equal objective vectors retain one representative. Without numerical objectives,
satisfaction backends return the first valid candidate.

These are fronts of **explored candidates**, not globally optimal solutions.
Search stops at its time, grammar, size or proposal limit. An in-flight compiler
check can overrun the nominal time budget; cvc5 and bounded Boolean search also
have process deadlines. Energy uses RAPL when available and the existing CPU-time
proxy otherwise. Resource comparisons therefore depend on the execution environment.

The regression suites exercise real searches and combinations, not just capability
flags: `specification_matrix_test.py`, `example_adapters_test.py`,
`specialized_specifications_test.py`, `runtime_specification_adapters_test.py`,
`synthesis_specifications_test.py`, and `synthesis_pareto_fallback_test.py`.
LLM candidate streams are mocked for repeatable integration tests; no live-provider
success rate or model-quality claim is made.

## Further work

* Expose an explicit mandatory/soft policy for fitness backends, preserving noisy
  observations while allowing required examples/properties to constrain acceptance.
* Feed objective improvements into candidate generation and recover safe PBE
  compression with richer observational signatures.
* Expand existing grammars (constructor CSV schemas, classification trees, richer
  recurrence alternatives, and joint Contata optimization) separately from the
  specification adapters.
