# Inductive reasoning for refinements over recursive bindings

Status: **design analysis / scope decision** for [issue #328]. No new
verification power is added; this document determines *whether and when*
induction is required, lays out the options, and fixes the scope.

This is the long-form answer to the `# TODO: induction?` markers that used to
sit on the `SRec` cases of `liquefy` (`aeon/sugar/lowering.py`) and
`liquefy_rec` (`aeon/core/substitutions.py`).

## TL;DR

Aeon does **not** do induction over recursive definitions, and for the common
case it does not need to. Three mechanisms cover recursive refinements today:

1. **Termination-gated typing** — a recursive call may be typed at its declared
   *refined* return type (the induction hypothesis) exactly when a well-founded
   `decreasing_by` metric is verified. This is the workhorse and is sound
   (shipped in #332).
2. **PLE (Proof by Logical Evaluation)** — bounded ground unfolding of reflected
   function applications, which discharges *concrete* facts like
   `factorial 3 = 6`.
3. **Refinement reflection** — a single **ground** equation `f(params) = body`
   per reflected function, fed to PLE.

What is genuinely out of reach is **universally-quantified inductive
properties** such as `forall n. factorial n >= 1`, because the SMT encoding is
strictly quantifier-free and there is no induction principle. The
recommendation is to **keep it that way for now**: state recurrences explicitly
in the refinement and let the metric discharge them, rather than adding
quantified axioms or an induction tactic.

## How recursion is reasoned about today

### Reflection is a ground equation, not a quantified axiom

`ReflectedFunctionDeclaration` (`aeon/verification/smt.py`) emits a single
ground premise for the function's *own parameter names*:

```python
app = LiquidApp(name, [LiquidVar(p) for p in params])
eq  = LiquidApp(Name("==", 0), [app, body])   # f(p1..pn) == body  — ground
yield from flatten(seq, nctx.with_premise(eq))
```

There is no `ForAll` anywhere in the SMT layer — the encoding handed to z3 is
quantifier-free. So the solver never has a universally instantiable rule for
`f`; it only has this one ground fact plus whatever PLE unfolds.

### PLE: bounded ground unfolding

`ple_unfold_fixpoint` (`aeon/verification/smt.py`) rewrites
`f(concrete_args)` to its body with arguments substituted, to a fixpoint,
bounded by:

- `max_steps = 256` unfolding iterations,
- `max_term_size = 4096` nodes (`size_guard`),
- a `repr`-based cycle detector (`seen_guard`),
- termination when no redex remains (`no_change`).

This proves ground/closed facts (`factorial 3 = 6`) but **cannot** establish a
property over an unbounded/symbolic argument: unfolding `factorial n` for
symbolic `n` never reaches a fixpoint and stops at a guard.

### Termination-gated induction hypothesis

This is the part that does the real work for recursive *specifications*. In
`synth`/`check` for `Rec` (`aeon/typechecking/typeinfer.py`), the recursive
occurrence is bound at its declared type **only when a metric is present**:

```python
rec_var_type = var_type if has_metric else _erase_return_refinement(var_type)
```

and `termination_metric_constraints` (`aeon/typechecking/termination.py`)
requires, at every recursive call, a strict lexicographic decrease **and**
non-negativity of the metric:

```
(entry /\ nested /\ branch)  =>  (m(call) <* m(entry)  /\  m(call) >= 0)
```

Soundness argument: by well-founded induction on the metric, assuming the spec
holds on all smaller inputs is legitimate, so typing the recursive call at the
declared refined type is sound. Without a metric the hypothesis is erased to the
bare codomain, so a non-terminating function cannot "prove" an absurd refinement
(regression-tested in `tests/recursion_soundness_test.py`).

### The `_` marker rejects self-reference

`reflect_underscore_in_definitions` (`aeon/sugar/desugar.py`) expands
`{y | _}` into `{y | y = body}`, but **rejects** a self-recursive body,
directing the user to state the recurrence explicitly — precisely because
reflecting a recursive body as a ground equation would need induction to be
useful.

## Determination: when is induction actually required?

| Goal | Needed today? | Mechanism |
|---|---|---|
| `factorial 3 = 6` (closed) | no | PLE unfolding |
| `double n : {r \| r = n + n}` with `decreasing_by [n]` | no | metric-gated IH |
| `f` total / terminates | no | termination metric |
| `forall n. factorial n >= 1` (open, inductive) | **yes** | *unsupported* |
| `forall xs. length (append xs ys) = length xs + length ys` | **yes** | *unsupported* |

Induction is required only for the last class: **universally-quantified
properties whose proof recurses on the structure/measure of the argument**.
Every other recursive-refinement need is already covered by stating the
recurrence in the return type and letting the verified metric discharge it.

## Options (and trade-offs)

### Option A — Status quo: explicit recurrence + metric *(recommended)*

Keep the ground/PLE/metric design. Users express recursive specs as recurrences
in the refinement (`{r | r = n + n}`) under `decreasing_by`.

- **+** Sound (shipped, tested), decidable, fully automatic, no quantifiers.
- **+** Matches Liquid Haskell's measure-based discipline.
- **−** Cannot state/prove open inductive lemmas; the spec must be a recurrence,
  not an arbitrary `forall`.

### Option B — Quantified axioms + z3 instantiation (e-matching)

Emit `forall params. f(params) = body` and let z3 instantiate via triggers.

- **+** Closer to "real" reasoning; some inductive facts fall out via
  instantiation + the recurrence.
- **−** Undecidable / unpredictable: trigger selection, matching loops,
  non-termination of the solver. A net loss of the current decidability and
  reproducibility. **Not recommended.**

### Option C — An explicit induction tactic in the proof language

Aeon already has a tactic/`by` layer. Add an `induction`-style tactic that, for
a goal `forall n. P n`, generates base/step subgoals (step assumes `P (n-1)`).

- **+** Sound, explicit, opt-in; no global SMT instability; composes with
  existing tactics.
- **+** Only pays for induction where the user asks for it.
- **−** Real implementation effort (subgoal generation, scheme selection for
  data types, integration with the VC pipeline). This is the natural home for
  future work if open inductive lemmas become a requirement.

### Option D — Structural measures / lemmas-as-functions

Encode inductive lemmas as ordinary (terminating, metric-checked) recursive
functions returning a proof-carrying `{p:Unit | property}`, leaning on the
existing metric-gated IH.

- **+** No new machinery; reuses Option A end-to-end.
- **−** Ergonomically heavy; the user hand-writes the induction as a function.
  Worth documenting as a *pattern* rather than building.

## Scope decision

1. **Do not** add quantified axioms to the SMT layer (Option B): it would forfeit
   the decidability and reproducibility that the current design guarantees.
2. **Keep** the termination-gated recurrence approach (Option A) as the supported
   way to specify recursive functions. Document the pattern (this file + the
   `_`-marker error message already point users there).
3. **Future work, opt-in only:** if open inductive lemmas (`forall n. P (f n)`)
   become necessary, add them as an explicit **induction tactic** (Option C),
   not as global solver behavior. Tracked as a follow-up; out of scope for now.

In short: the `# TODO: induction?` markers resolve to *"intentionally not done;
recurrence-in-refinement + metric covers the need, and full induction is a
future opt-in tactic."*

[issue #328]: https://github.com/alcides/aeon/issues/328
