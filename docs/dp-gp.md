# Dynamic-programming synthesis with GP components

`-s dp_gp` transforms a supplied finite reference generator into an executable
Aeon algorithm. Native genetic programming searches small transformation
components: a pruning relation, solution projection and incremental updates,
memoization keys, and a search-state projection. It uses the existing GP engine,
including crossover, mutation, selection and elitism.

```bash
python -m aeon --no-main --budget 30 -s dp_gp examples/synthesis/dp_gp/knapsack.ae
python -m aeon --no-main --budget 30 -s dp_gp examples/synthesis/dp_gp/path.ae
```

## Source contract

An explicit reference declaration applies the standard `DP.reference` combinator:

```aeon
def reference(n:Int)(capacity:Int):Int :=
  DP.reference n n capacity 0 allowed next_x next_y next_z
    gain used count objective 0 0 0 0;
@dp_gp(reference, 4, 5)
def optimized(n:{v:Int | v >= 0 && v <= 4})
             (capacity:{v:Int | v >= 0 && v <= 5}):Int := ?algorithm;
```

The arguments to `DP.reference` are, in order:

| Arguments | Meaning |
| --- | --- |
| fuel | First input; decreases by one at every recursive call |
| three initial state fields | Scalar expressions over the two inputs |
| allowed | Three state fields and action (0 or 1) → Bool |
| three next-state functions | Three state fields and action → Int |
| three solution contributions | Three state fields and action → Int |
| objective | Three solution fields → Int, maximized |
| three base values | Int literals for the depth-zero solution |
| floor | Int literal below every feasible objective |

The generator explores every legal branch. On return from a child, it adds the
branch's contributions to that child's solution fields. States and solutions
start with three fields; emitted representations can have fewer. The supplied
reference remains intact and is executed as the correctness oracle.

The target must have two independently bounded nonnegative Int parameters and
one unnested Int body hole. Its interval refinements must exactly match the
annotation bounds. Every input must have at least one feasible solution. The
initial fragment returns optimum values; witness reconstruction and specified
tie behavior are unsupported. Knapsack legality is expressed in `allowed`;
there is no knapsack-specific logic in the backend. The path example instead
changes a graph vertex at each action.

Reference scalar functions may use finite literals, arguments, acyclic helpers,
let, if, arithmetic `+ - *`, integer/Boolean comparisons and Boolean operations.
Native calls, effects, recursion in components, opaque functions, arbitrary
recursive generators, ADT input data, additional optimization/property goals,
and coupled holes are explicit capability errors. General non-additive solution
constructors are outside this fragment. There is no whole-program GP fallback.

## Transformation obligations

1. **Thinning:** GP chooses a conjunction of omitted/equal/ascending/descending
   comparisons on the three solution fields. This grammar constructs preorders.
   Z3 checks objective compatibility and preservation under every additive
   extension. Comparisons happen only within the same subproblem. Insertion
   keeps one existing representative on equivalence, avoiding deletion of an
   entire equivalence class.
2. **Solution representation:** GP chooses a projection and incremental update
   expressions from `old`, `delta`, `0`, `1`, `old+delta`, `old-delta`, and
   `old*delta`. Retained fields must support every objective/relation query.
   Z3 checks each update's commutation with the original constructor. Components
   are accepted together, so a smaller representation cannot bypass its updates.
3. **Memoization:** GP searches state projections, minimizing distinct keys.
   Any collision must preserve the entire represented, thinned frontier, not
   just its best objective. Fuel is always included. Caches are local to one
   algorithm invocation; states from separate instances are never conflated.
4. **State representation:** GP searches a smaller projection. Dependency checks
   require closure under the selected transitions, legality, contributions and
   memo key. Corresponding transition/query code is derived by substituting
   projected field accesses, establishing commutation by construction.

Each stage minimizes its cost only among training-admissible components.
New SMT counterexamples or incompatible memoized states revise the relevant
fitness cases and restart GP with fresh caches and populations. Unknown SMT
results and incomplete searches fail; they do not establish equivalence.

## Assurance and evaluation

The seed deterministically partitions the finite input box: approximately one
quarter for initial GP training, one quarter held out, and the remainder for
counterexample discovery. Held-out inputs never enter GP fitness or
counterexample feedback. After search, every input in the declared box is
checked against both the executable reference and the emitted Aeon algorithm.
A held-out failure rejects the algorithm. Normal whole-program type/refinement
checking remains mandatory. Fuel decreases and generated vector/frontier/cache
traversals are finite; GP components contain no recursion or effects.

Reports distinguish universal scalar transformation obligations (SMT or grammar/
dependency construction) from **exhaustive equivalence on the finite input
domain**, including bounded memoization safety. They make no universal claim
outside that domain, PAC bound, asymptotic improvement or published speedup claim.

`DPSynthesizer.last_report` records the component plan, per-stage generations,
assessments, counterexamples, seeds, split indices, stop reason and deterministic
costs. Ablations compare the untransformed reference, thinning alone, and all
four stages. `calls` counts expanded states; `cache_hits` counts reused states;
`retained` sums retained frontier entries. `solution_cells` counts constructed
solution fields; `state_cells` includes states constructed before cache hits.
They are modeled construction counts, not measured bytes or elapsed runtime.
Library list scans and key-table lookup costs are not represented by these
metrics. The pure memo table uses linear lookup, not a constant-time hash table.

```bash
PYTHONPATH=. python scripts/bench_dp_gp.py --output /tmp/dp-gp-results \
  --budget 30 --proposals 160 --seeds 0 1 2
python -m pytest tests/dp_gp_test.py tests/genetic_programming_synthesis_test.py -q
```

The runner writes reports and generated `.ae` programs, recompiles the saved
programs in a fresh driver, and checks every declared input again. Failed runs
remain in the report. No end-to-end GP performance ranking is inferred: the
component grammar and the unrestricted program grammar search different spaces.

## Configuration and limits

Use `AEON_SEED` plus these environment variables:

| Variable | Default | Meaning |
| --- | ---: | --- |
| `AEON_DP_GP_PROPOSALS` | 600 | Assessments per stage/fitness epoch |
| `AEON_DP_GP_EPOCHS` | 8 | Counterexample refinement attempts per stage |
| `AEON_DP_GP_MAX_NODES` | 100000 | Reference/checking work meter |
| `AEON_DP_GP_MAX_FUEL` | 8 | Largest first-input bound |
| `AEON_DP_GP_MAX_INSTANCES` | 128 | Largest exhaustive input box |

Component GP uses a fixed population of 32 for reproducibility under a proposal
limit. Ordinary GP retains its existing adaptive population and behavior. One
global synthesis deadline covers reference execution, search, checking and final
validation. A contained worker is terminated at expiration; only a completely
checked algorithm is returned. Compilation before synthesis and process teardown
add overhead, so this is not a hard real-time bound.

The stage ordering and preservation obligations adapt the thinning and three
representation/key rules in [Automating Thinning Theorem](https://arxiv.org/abs/2202.12208),
sections 3–6. This implementation substitutes GP for the paper's component
solvers and supports a smaller additive generator/projection fragment. It does
not reproduce MetHyl+'s full languages, AutoLifter, witness contracts, PAC
procedure, or benchmark results. Counterexample feedback follows the general
approach of [counterexample-driven GP](https://www.ijcai.org/proceedings/2018/742).
