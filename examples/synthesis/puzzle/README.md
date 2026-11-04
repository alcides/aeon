# Constraint and synthesis puzzles

Nineteen problems specify a satisfying or optimal value, assignment, or circuit
using refinements and synthesis objectives.

| Programs | Task |
| --- | --- |
| [bank_deposit.ae](bank_deposit.ae), [stock_profit.ae](stock_profit.ae) | Deposit planning and buy/sell optimization |
| [candy_contribution.ae](candy_contribution.ae) | Contributions satisfying a shared purchase target |
| [circle_points.ae](circle_points.ae), [distinct_triples.ae](distinct_triples.ae) | Integer points and equal-sum/equal-product triples |
| [coin.ae](coin.ae), [knapsack.ae](knapsack.ae) | Coin change and item selection |
| [cryptarithmetic.ae](cryptarithmetic.ae) | TWO + TWO = FOUR with distinct digits |
| [linear_equation.ae](linear_equation.ae), [quadratic.ae](quadratic.ae), [system_equations.ae](system_equations.ae), [pell_equation.ae](pell_equation.ae) | Arithmetic equations |
| [magic_square.ae](magic_square.ae), [nqueens.ae](nqueens.ae), [map_coloring.ae](map_coloring.ae) | Grid, board, and graph constraints |
| [nurse_scheduling.ae](nurse_scheduling.ae), [scheduling.ae](scheduling.ae), [shift_assignment.ae](shift_assignment.ae) | Staff and job scheduling |
| [nand_full_adder.ae](nand_full_adder.ae) | NAND-only adder synthesis with minimum depth |

These include locally encoded classic problems and tutorial/blog adaptations.
Original source attributions remain in their headers and in the
[local synthesis overview](../README.md). Pizza assignment and page layout are
grouped with [level design](../leveldesign/README.md).

Run from the repository root:

```bash
python -m aeon --check --no-main examples/synthesis/puzzle/nqueens.ae
python -m aeon --no-main --budget 30 -s gp examples/synthesis/puzzle/nqueens.ae
```
