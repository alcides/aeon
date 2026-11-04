# ARC-inspired grid tasks

Seven Aeon examples inspired by ARC Prize grid transformations. Each encodes a
fixed 3×3 input/output task using an inductive grid, a refined output hole, and a
completed output satisfying the same refinement.

| Program | Transformation |
| --- | --- |
| [arc_grid_transform.ae](arc_grid_transform.ae) | Horizontal mirror |
| [arc_vertical_mirror.ae](arc_vertical_mirror.ae) | Vertical mirror |
| [arc_rotate90.ae](arc_rotate90.ae) | Clockwise quarter-turn |
| [arc_rotate180.ae](arc_rotate180.ae) | Half-turn |
| [arc_transpose.ae](arc_transpose.ae) | Matrix transpose |
| [arc_recolor.ae](arc_recolor.ae) | Swap two colors |
| [arc_gravity.ae](arc_gravity.ae) | Drop colored cells within each column |

The source headers cite ARC Prize 2024, but do not record original task IDs.
These are locally constructed adaptations. The hole produces one output grid;
it does not learn a general transformation from training pairs or evaluate on
held-out ARC tasks.

Run from the repository root:

```bash
python -m aeon --check --no-main examples/benchmarks/arc/arc_gravity.ae
python -m aeon --no-main --budget 30 -s gp examples/benchmarks/arc/arc_gravity.ae
```
