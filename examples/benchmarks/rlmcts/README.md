# RL-MCTS demos

- [rl_mcts.ae](rl_mcts.ae): synthesize a bounded integer and an identity function
  from refinement contracts.
- [rl_mcts_training.smt2](rl_mcts_training.smt2): a universally valid arithmetic
  formula used by the SMT task-generation and training demo.

These are local examples of the RL-MCTS backend, not the paper's experimental
corpus. See the [backend and training documentation](../../../docs/synthesizers.md#rl_mcts--reinforcement-learning-guided-grammar-tree-search).

Run from the repository root:

```bash
python -m aeon -s rl_mcts --budget 10 examples/benchmarks/rlmcts/rl_mcts.ae
python -m aeon.synthesis.modules.rl_mcts generate \
  examples/benchmarks/rlmcts/rl_mcts_training.smt2 --output /tmp/aeon-rl-data
```
