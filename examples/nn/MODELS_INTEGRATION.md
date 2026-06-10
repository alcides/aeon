# Integrating NN with Learning via typeclasses

A classifier typeclass and a regressor typeclass that **both** the
neural-network models (`NN.Network`) and the scikit-learn-backed `Learning`
models (`SklearnClassifier` / `SklearnRegressor`) implement, so the same code
drives either kind of model.

## What's here

* **`libraries/Models.ae`** — `Classifier` (the classifier typeclass) and
  `Regressor` (the regressor typeclass), with instances for `NN.Network`
  *and* `Learning`'s `SklearnClassifier` / `SklearnRegressor`. `classify` /
  `regress` / `cls_classes` / `cls_inputs` / `reg_inputs` dispatch by the
  model's type. The shared feature representation is a `Tensor.Vector` (one
  sample).
* **`examples/nn/models.ae`** — runs a neural network and a `sklearn`
  decision tree through the *same* `classify` / `cls_classes` calls.
* **`Learning.ae`** — gains single-sample, `Vector`-based entry points
  (`classify_one`, `regress_one`, `clf_n_features`, `clf_n_classes`,
  `reg_n_features`) so a fitted model can satisfy the classes.
* **`NN.ae`** — gains `predict_unchecked` / `predict_scalar` (forward without
  the static `dim` precondition) as the generic methods' entry points.

The typeclasses take the natural names `Classifier` / `Regressor`. `Learning`'s
opaque model *types* were therefore renamed to the more specific
`SklearnClassifier` / `SklearnRegressor` (they are fitted scikit-learn
estimators): a class and a type sharing one name collide on a single z3 sort,
and the rename also reads better — `instance : Classifier SklearnClassifier`
says "a fitted sklearn classifier is a Classifier".

## Interpreter fixes that made it possible (`aeon/sugar/desugar.py`)

1. **Concrete instance heads over opaque types.** The parser turned every
   non-builtin bare type name into a type *variable*, so `instance : C
   Network` was silently polymorphic over a variable named `Network` and
   method bodies saw an abstract `'Network` that wouldn't unify with the
   imported type. Instance desugaring now promotes an upper-case head name
   (not bound by the instance's constraints) to a concrete constructor.

2. **Binder-aware name resolution (the name-collision fix).** Import
   resolution rewrote *any* bare name found in the combined unqualified scope
   to its module-prefixed form — **without respecting local binders**. So
   `NN.train_step`'s parameter `target` was captured as `Learning.target`,
   and `Learning`'s refinement variable `rows` as `Tensor.rows`, the moment
   both libraries were loaded. The three resolvers now thread a `bound` set
   (function parameters, `let` / `fun` / `match` binders, refinement and
   dependent-type binders) and never rewrite a locally-bound name. A
   library's own internal references are still module-qualified; only its
   local binders are now shielded — so imported modules no longer interfere.

3. **`native_import` hoisting.** A `native_import` def binds a global Python
   symbol (e.g. `np`) that other modules' native bodies use by bare name. The
   runtime builds a let-chain from the def list and a closure only captures
   bindings introduced before it; when `Learning` re-imports `Tensor`, the
   import walk could place a consumer (`NN.dense_relu`) ahead of its provider
   (`Tensor`'s `np`). `native_import` defs are now hoisted to the front of
   the let-chain, so those globals are available regardless of import order.

All three are pure additions to resolution/ordering; the full suite passes.

## Honest remaining limitations

* **Typeclass methods are SMT-opaque** (the caveat `Num.ae` documents). So
  the dimension/shape/metric invariants that `Tensor` / `NN` / `Learning`
  verify on their *concrete* operations are not carried as laws through these
  generic methods — `classify` takes an unconstrained `Vector` and a width
  mismatch is a runtime error. `Models` is a dispatch/reuse surface; drop to
  `NN.predict` / `Learning.accuracy` directly when you need the static
  guarantee.
* **No polymorphic-over-constraint dispatch.** A function written generically
  as `def f [Classifier m] (model: m) … := classify model …` does not resolve
  the method from the `[Classifier m]` dictionary (it reports "no instance
  for `<unknown>`"). Dispatch works on concrete model types
  (`classify net …`, `classify tree …`), which is what the example uses.
  Making the class dictionary drive method resolution inside a constrained
  generic is a separate typeclass-elaboration improvement.
