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

## Full published MSR dataset

The paper's corpus is hosted at the
[MSR dataset page](https://msr-redmond.github.io/karel-dataset/), not in the
carpedm20 generator repository. Section 6.1 of
[Bunel et al., ICLR 2018](https://arxiv.org/abs/1805.04276) specifies one million
training tasks, another 5,000 tasks split between validation and test, and six
ordered I/O examples per task. The first five are the specification; the sixth
is held out. Newly generated worlds/programs are not substitutes for these records.

The importer processes **every record** of extracted `train.json`, `val.json`,
and `test.json` (JSONL, also `.jsonl`/gzip supported). Unknown syntax, invalid
grids, conflicting JSON/tensor representations, or incorrect example counts
fail with a source line number instead of dropping tasks. Manifests record
source SHA-256 digests, counts, GUIDs, and original split/example order.
Challenge splits can be included with `--splits`; specify their actual example
counts rather than assuming the synthetic six-example protocol.

A surviving [validation mirror](https://huggingface.co/datasets/akdo00001/dataset_Karel)
contains all 2,500 validation tasks, with six examples each and distinct GUIDs.
The fetch command pins its revision, archive hash, and decompressed JSONL hash:

```bash
python scripts/import_karel_dataset.py fetch-validation --out /tmp/karel-source
python scripts/import_karel_dataset.py import --source /tmp/karel-source \
  --out /tmp/aeon-karel-validation --splits val
python -m aeon.benchmarks.karel_runner --split /tmp/aeon-karel-validation/val \
  --jobs 8 --results /tmp/karel-val-results.jsonl
```

This mirror supplies **validation only**, not training or test. Its exact bytes
are pinned; the unavailable original archive prevents independently proving
byte-for-byte identity to that host.
All 2,500 translated validation references have been compiled and executed in
Aeon against all six examples: **15,000 whole-world comparisons, zero failures**.
The checked-in [validation report](published/validation-report.json) records
the exact source hashes and coverage. This validates the translation/runtime,
not the synthesizer's ability to solve all those tasks.

```bash
python scripts/import_karel_dataset.py import \
  --source /path/to/1m_6ex_karel --out /tmp/aeon-karel-corpus --require-paper-size

# Optional: emit reference.ae and synth.ae (with ?hole) for EVERY test task.
python scripts/import_karel_dataset.py materialize \
  --split /tmp/aeon-karel-corpus/test --out /tmp/aeon-karel-tasks

# Execute every translated reference in Aeon against all six examples.
python -m aeon.benchmarks.karel_runner \
  --split /tmp/aeon-karel-corpus/test --results /tmp/karel-reference-results.jsonl

# Synthesize from five examples, then independently evaluate the sixth.
python -m aeon.benchmarks.karel_runner --mode synthesize --synthesizer enumerative \
  --budget 60 --deadline 120 --split /tmp/aeon-karel-corpus/test \
  --results /tmp/karel-synthesis-results.jsonl
```

Repeat validation for `train` and `val`. Neither runner nor importer implicitly
subsamples. `--start`/`--count` allow explicit shards. Results report consistency
separately from generalization; errors/timeouts count as failures. Summary files
distinguish whole-split validation from subsets. Existing outputs are not overwritten.

Converted splits are indexed, disk-backed JSONL: a million-task index uses
approximately 8 MB rather than eagerly loading all worlds. Materializing all
million task directories is optional and expensive; the runner streams without
creating them. Observed examples, held-out examples, and references live in
separate files. Synthesis files import only DSL operations and hide the
specification variable inside the hole, with no reference function, world
constructor, or held-out examples in the candidate context.

Published tensors are sparse **channel-first** 16×18×18, bottom-up, with N/E/S/W
direction channels and explicit padding boundaries, unlike carpedm20's encoding.
References translate to Aeon combinators; Python does **not** interpret their
control flow. Published worlds use crash semantics (blocked moves/empty picks
fail), allow intermediate marker stacks through 101, and share a 200-tick budget
across actions, conditions, and repeat iterations, matching `Consistency` in
[the authors' artifact](https://github.com/bunelr/GandRL_for_NPS/tree/5ff32d9e179d52e1353ff0b9a5c11f948c9ad188).
The ten earlier regression tasks retain carpedm20's no-op behavior.

**Availability/validation status:** the complete published corpus has not been
acquired or validated: training and test remain unavailable. The official
OneDrive links returned HTTP 403 (the anonymous share API returned 401), and
the later nearai/SED S3 mirror returned HTTP 404. A working full archive or
mirror is still required. The adapter also has labeled format fixtures testing
actual Aeon reference execution and synthesis. Matching counts alone does not
prove provenance or reference correctness.

## Additional carpedm20 generator datasets

The domain and encoding follow [carpedm20/karel](https://github.com/carpedm20/karel),
revision `ee29de7460f0e6f24ea542d6cf8e44b88694ef1a`, linked by issue #564.
Its generator defaults are 1,000,000 training programs, 5,000 validation/test
programs each, 8-by-8 worlds, grammar depth 5, repeat constants 0–19, and a
100-call interpreter budget. Its `num_examples` option defaults to 2 but is
unused: the committed generator emits one I/O pair per program.

These generated datasets are **not the published MSR corpus**. Generate them
using the source repository's `generate.py` and load its
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
