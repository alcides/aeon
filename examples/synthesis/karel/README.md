# Embedded 2D Karel benchmarks

Karel programs are ordinary Aeon functions of type `(w: World) -> World`.
The `Karel` standard library supplies the five actions, all five spatial/marker
predicates, negation, sequencing, repetition, conditionals, and bounded while
loops. Program composition and synthesis holes are written in Aeon.

```aeon
import Karel;
open Karel

# An empty 5-by-3 grid, robot at (0, 1), facing east.
def initial : World :=
    with_markers (with_wall (world 5 3 0 1 east) 3 0) 2 1 2

def walk (w: World) : World := while_karel 19 front_is_clear move w
def collect (w: World) : World := while_karel 19 markers_present pick_marker w
def walk_and_collect (w: World) : World := sequence walk collect w
```

Coordinates start at the top left: x increases east and y increases south.
Directions are `north`, `east`, `south`, and `west`. All world edits return new
values. Walls and boundaries block movement; blocked moves and picking an
empty cell leave the state unchanged. Markers are per cell, with counts 0–10
to match the source's tensor format. Placing an eleventh marker is a failed
candidate. Rendered robot glyphs hide any markers beneath the robot;
`same_world` and `fitness` compare the complete state, including those markers.

`while_karel fuel predicate body` raises when the guard is still true after
the budget is exhausted. `fitness` counts that execution as a failed example,
along with invalid actions and wrong output states. Zero fitness means every
whole-world I/O example matched.

## Checked-in tasks

`reference/` contains ten executable programs with independently constructed
expected worlds. `synth/` contains the same ten tasks with `?hole` bodies:
move, turn, pick, put, repeat, conditional movement around a wall, walking to a
wall/boundary, harvesting marker stacks, and left/right clearance branches.
Each task has two I/O examples. These are Aeon regression tasks, not a claimed
copy of a published fixed dataset. The source repository generates its dataset.

```bash
python -m aeon examples/synthesis/karel/reference/while.ae
# Prints 0.0 (all I/O examples match).
python -m aeon --no-main -s enumerative --budget 5 examples/synthesis/karel/synth/move.ae
# Finds move w with fitness 0.0.
```

Larger compositions can require longer synthesis budgets. All reference
solutions execute and every hole-bearing task parses and typechecks in tests.
Input/output globals are shadowed inside the holes to keep expected states
out of the candidate grammar.

## Source datasets

The domain and encoding follow [carpedm20/karel](https://github.com/carpedm20/karel),
revision `ee29de7460f0e6f24ea542d6cf8e44b88694ef1a`, linked by issue #564.
Its generator defaults are 1,000,000 training programs, 5,000 validation/test
programs each, 8-by-8 worlds, grammar depth 5, repeat constants 0–19, and a
100-call interpreter budget. Its `num_examples` option defaults to 2 but is
unused: the committed generator emits one I/O pair per program.

Generate datasets using the source repository's `generate.py` and load its
`train.npz`, `test.npz`, or `val.npz` directly in Aeon:

```aeon
import Karel;
open Karel
def data : Dataset := load_dataset "data/test.npz"
def training : Examples := dataset_task data 0

@minimize(fitness solve training)
def solve (w: World) : World :=
    let data := unit in let training := unit in ?hole
```

The loader accepts `N × H × W × 16` and `N × E × H × W × 16` I/O arrays,
validates every world, and ignores stored source program tokens. Direction
channels follow the source's north/south/west/east order; wall channel is 4,
and marker-count channels are 5–15. NumPy is already an Aeon dependency.
Python callers can use `aeon.bindings.karel.to_tensor` and `from_tensor` to
interoperate with source datasets.

`random_world width height seed` provides reproducible Aeon worlds using the
source's default wall and marker probabilities (0.1), border walls, and one
marker per sampled cell. It uses a different random generator, so its seeds
do not reproduce the source's NumPy samples. The published generator's call
budget and Aeon's explicit loop fuel are also different counting conventions;
this port does not claim comparable timing or search results.
