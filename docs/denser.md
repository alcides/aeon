# DENSER neural architecture synthesis

The [DENSER benchmark](../examples/synthesis/denser/README.md) defines the
Genetics_ANN CNN grammar as a refined Aeon ADT. MNIST and CIFAR-10 tasks leave
an architecture hole and maximize real held-out validation accuracy; an
additional Pareto objective minimizes trainable parameter count.

Refinements check dimensions, layer phases, dataset choice and hyperparameter
domains. Accuracy remains an empirical numerical objective, not a theorem or
axiom. The benchmark includes pinned reference provenance, checked controls,
negative refinement tests, property-based shape/count tests, and a bounded
synthesis/training smoke test. Full datasets and tensor dependencies are
optional; no download happens during CI. See the benchmark README for scope,
reference-runtime differences, and runnable commands.
