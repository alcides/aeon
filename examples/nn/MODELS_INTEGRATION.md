# Integrating NN with Learning via typeclasses — status & findings

Goal: a classifier typeclass and a regressor typeclass that both the
neural-network models (`NN.Network`) and the `Learning` models
(`Learning.Classifier` / `Learning.Regressor`) implement, so code can be
written once against "any classifier" / "any regressor".

## Delivered

* **`libraries/Models.ae`** — `Categorical` (classifier) and `Continuous`
  (regressor) typeclasses, with `NN.Network` as an instance of both.
  `classify` / `regress` / `n_classes` / … dispatch by model type. See
  `examples/nn/models.ae` (runs).
* **`NN.predict_unchecked` / `NN.predict_scalar`** — forward passes without
  the static `dim x == net_in` precondition, the entry points the generic
  (model-agnostic) methods dispatch to.
* **Interpreter fix (`aeon/sugar/desugar.py`)** — the enabler. The parser
  turns every non-builtin bare type name into a *type variable*, so
  `instance : C Network` was silently read as polymorphic over a variable
  named `Network`, and method bodies saw an abstract `'Network` that would
  not unify with the concrete imported type. Instance desugaring now
  promotes an upper-case head name that is not bound by the instance's
  constraints to a concrete constructor. **Full suite: 1477 passed, 0
  failed.** This makes typeclass instances over *any* opaque/imported type
  work, not just NN's.

## Why `Learning` is not yet an instance (the honest blockers)

Two further Aeon limitations stop the *bidirectional* integration, both
independent of the fix above:

1. **Typeclass methods are SMT-opaque.** Methods are dictionary
   projections, invisible to the SMT backend (the same caveat `Num.ae`
   documents). So the shape/metric *laws* that are the whole point of these
   libraries — `dim x == net_in net`, `accuracy ∈ [0,1]`, `mse ≥ 0` —
   cannot be carried as verified refinements through a generic method.
   `Models` is therefore a dispatch/reuse surface, not a verified one;
   `classify` takes an unconstrained `Vector` and a width mismatch is a
   runtime error.

2. **`Tensor` and `Learning` cannot be loaded together.** Aeon
   re-elaborates a module's source on import, and `Tensor` and `Learning`
   share unqualified names (`rows`, `cols`, `target`, `np`). Opening both
   (directly, or transitively via `NN`) mis-resolves them — e.g.
   `NN.train_step`'s local `target` binds to `Learning.target`, and
   `Learning`'s `rows` binds to `Tensor.rows` — so a program that uses both
   an NN model and a Learning model fails to elaborate. This is a
   library-namespace collision, not a typeclass issue, but it blocks any
   single program from holding both instance families.

## What would unblock it

* For (2): qualify or rename the colliding exports (`Tensor.rows/cols` →
  measures that don't collide; `Learning`'s `target`/`rows` similarly), or
  give Aeon's importer proper per-module name isolation so re-elaboration
  cannot capture another module's binders. Once both libraries co-load, a
  `Learning` instance is straightforward:
  `instance : Categorical Classifier where classify model x := <predict_proba on one sample>` (needs thin single-sample `Vector` bindings added to `Learning.ae`).
* For (1): a way to expose a method's refinement to the SMT backend (reflect
  the dictionary projection), or model-shape *measures* declared at the
  class level — a larger typeclass/elaboration change.

The NN-side typeclasses are designed so that adding the `Learning`
instances is a drop-in once (2) is resolved — the class names
(`Categorical`/`Continuous`) were chosen specifically to avoid clashing
with `Learning`'s `Classifier`/`Regressor` *types*.
