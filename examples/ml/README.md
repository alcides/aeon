# Machine-learning synthesis benchmarks

The `Learning` examples demonstrate Aeon's typed dataset and estimator API.
The `amltk_*` benchmarks adapt workflows from the
[AutoML Toolkit](https://github.com/automl/amltk) into Aeon synthesis problems.
Each declares one pipeline-expression hole and a `@maximize_float` goal.
Aeon's synthesizer composes typed building blocks to fill that hole.
Python FFI functions construct, fit, and score scikit-learn objects.

| Benchmark | Stated synthesis goal | Pipeline internals searched | Upstream reference |
| --- | --- | --- | --- |
| `amltk_hpo.ae` | Maximize validation accuracy | Mean/median imputation; no/standard/min-max scaling; forest depth 1/3/5 | [HPO](https://automl.github.io/amltk/latest/examples/hpo/) |
| `amltk_cv.ae` | Maximize mean three-fold stratified CV accuracy | Same preprocessing; forest depth 1/3/5 or linear/RBF SVC | [CVEvaluation](https://automl.github.io/amltk/latest/examples/sklearn-hpo-cv/) |
| `amltk_ensemble.ae` | Maximize validation accuracy | Both member pipelines from the CV grammar; mixture weight 0, 0.25, 0.5, 0.75, or 1 | [Post-hoc ensembling](https://automl.github.io/amltk/latest/examples/hpo_with_ensembling/) |

Run from the repository root with the development environment active:

Install the optional ML dependencies with `uv pip install -e ".[ml,tests]"`
in the project virtual environment, or use `.[dev]` for the full development
toolchain.

```bash
python -m aeon --budget 15 -s enumerative examples/ml/amltk_hpo.ae
python -m aeon --budget 20 -s enumerative examples/ml/amltk_cv.ae
python -m aeon --budget 30 -s random_search examples/ml/amltk_ensemble.ae
```

The CLI displays the synthesized expression and its objective fitness. It does
not automatically execute `main` after synthesis. Each benchmark defines `main`
to print its selection score and final test accuracy and return test accuracy.
To synthesize and run a benchmark together, use the driver API:

```python
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

driver = AeonDriver(AeonConfig(
    synthesizer="random_search", synthesis_ui=SilentSynthesisUI(), synthesis_budget=15,
))
assert not list(driver.parse(filename="examples/ml/amltk_hpo.ae"))
assert driver.has_synth()
driver.synth()
assert not driver.has_synth()
test_accuracy = driver.run()
```

The goals are optimization objectives, not hard accuracy thresholds. A budgeted
run returns its best discovered candidate; it need not find the global optimum.
The budget is checked between search steps, so total elapsed time can exceed it.

For example, a synthesized single-model expression can be:

```aeon
assemble median_imputer standard_scaler medium_forest
```

An ensemble expression composes `blend` with two independently chosen
`assemble` expressions and a weight terminal. There are 18 single-model HPO
compositions, 30 CV compositions, and 4,500 ordered ensemble compositions
(including equivalent or redundant mixtures). The types require imputation,
scaling, and an estimator in that order and limit ensembles to two members.
These benchmarks search expressions within this supplied grammar; they do not
synthesize arbitrary sklearn code or invent new preprocessing algorithms.

All use bundled `data/iris.csv` and fixed random seeds, with no downloads or
additional dependencies beyond the project's pandas and scikit-learn dependencies.
HPO and ensemble use stratified 60/20/20 train/validation/test partitions. CV
reserves 20% for final testing and searches using three folds of the remaining
80%. Each evaluation fits a fresh clone; CV clones the whole pipeline per fold.
Imputation and scaling learn only from training rows. Test scores never enter
the synthesis objective. After selection, the complete synthesized pipeline is
refitted on all development rows for one final test evaluation.

These are educational adaptations. Aeon replaces the upstream optimization
loops; the ensemble uses a two-member probability mixture rather than Caruana's
greedy selection. Numeric Iris features replace mixed categorical/numeric
OpenML data. Scheduling, trial persistence, distributed execution, and MNIST
are outside their scope. The programs do not import amltk. Their opaque FFI
types trust Python operations: types constrain component composition, but do
not prove dataset provenance or preprocessing correctness across the FFI.
