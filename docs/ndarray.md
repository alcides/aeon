# Ranked multidimensional arrays

`open NDArray` provides owned, contiguous arrays with one shared implementation
for ranks one, two, and three:

| Type | Coordinates |
| --- | --- |
| `(NDArray Int Rank1)` | element |
| `(NDArray Int Rank2)` | row, column |
| `(NDArray Float Rank3)` | depth, row, column |

The element type and rank are static. Dimension sizes are runtime metadata and
can be constrained by refinements through method calls such as `array.ndim`,
`array.elements`, and `array.dimension_size axis`.
Every array is linear: bind it with `let 1` or accept it with `(1 array: ...)`.
These types are separate from the older NumPy-backed `Tensor.Matrix` API.

## Construction and indexing

`full1 n value`, `full2 rows cols value`, and `full3 depth rows cols value`
construct arrays on the host. All dimensions and the total element count fit
Aeon's non-negative 32-bit `Int` range. Zero-length dimensions are supported.

`get1`, `get2`, and `get3` consume the array and return an element. `set1`,
`set2`, and `set3` consume and return the updated array, retaining its shape.
Their index refinements require each coordinate to be within its own dimension.
Compiled indexing also checks bounds before accessing memory. `dimension`
consumes an array and returns a dimension witness; `count` returns its element
count. `discard` consumes an array without returning its data.

```aeon
open NDArray

def main (args: Int) : Int :=
    let 1 matrix := full2 2 3 7 in
    let 1 updated := matrix.set2 1 2 42 in
    updated.get2 1 2;
```

## Converting to 1D and back

`to_1d` works on every rank and returns `(NDArray a Rank1)`. `from_1d2`
and `from_1d3` accept a rank-one array and the desired dimensions. The
dimensions' product must equal the original element count. Statically known
incompatible shapes are type errors; runtime reshapes check the same invariant.

Conversions transfer ownership without copying element storage. The old
descriptor cannot be reused. Data retain row-major order: the last coordinate
varies fastest. An empty flat array can be reshaped to any valid empty shape;
the caller supplies those dimensions because a flat array cannot remember the
original multidimensional shape.

```aeon
let 1 matrix := full2 2 3 7 in
let 1 flat := matrix.to_1d in
let 1 matrix_again := flat.from_1d2 2 3 in
let 1 flat_again := matrix_again.to_1d in
let 1 volume := flat_again.from_1d3 1 2 3 in
volume.get3 0 1 2
```

`from_array` transfers an existing linear `(Array a)` into a rank-one NDArray.
`to_array` transfers a rank-one NDArray back to `(Array a)`. Apply `to_1d`
first to export a matrix or volume. These two storage bridges and constructors
run on the host; indexing, fill, dimension witnesses, and ranked reshapes also
work inside `@llvm` and `@gpu` functions.

See [`ndarray_reshape.ae`](../examples/llvm/ndarray_reshape.ae) for a complete
example with both 2D and 3D conversions.

## GPU kernels

The shape is part of the parameter, so callers do not flatten matrices or
provide a separate element count:

```aeon
open NDArray

@gpu
def zero_matrix (1 matrix: (NDArray Int Rank2)) :
    {r:(NDArray Int Rank2) |
        r.dimension_size 0 = matrix.dimension_size 0 &&
        r.dimension_size 1 = matrix.dimension_size 1} :=
    matrix.fill 0;
```

A direct `fill` entry point uses a parallel launch: a 1D, 2D, or 3D thread
grid according to the array's rank. Each thread writes one element, and bounds
checks cover partial blocks. Empty arrays still return their descriptor.
`fill` inside a larger compiled function uses a sequential loop; arbitrary
functions are not automatically parallelized. Launch dimensions are separate
from the rank representation. CUDA fills currently use blocks of 256, 16×16,
or 8×8×4 threads, with CUDA's 65535-block limit on the y/z grid axes.

`matrix.map_rows callback` consumes and returns a rank-two matrix. The callback
receives a row index and an owned rank-one row, and must return that row with
the same shape. A direct `map_rows` entry point launches one CUDA thread per
row in blocks of 256 threads. The callback writes only its own row; captured
snapshots must be read-only. Compiled callbacks use an inline two-argument
lambda, which can call separately compiled helpers. Capturing other owned
NDArray values is rejected. For example, the N-body entry point uses:

```aeon
output.map_rows (fun i => fun row => advance_body xs n i dt softening row)
```

Each thread has a private row descriptor pointing into the original matrix,
so row mapping copies no device element storage. Partial blocks are guarded,
and empty matrices still return their descriptor. Row bounds and reshape errors
propagate atomically into the parent descriptor. On the CPU, rows are processed
in a loop; the interpreted implementation passes independent row copies to the
callback and writes their results back. `map_rows` nested inside a larger GPU
function also uses a sequential loop; parallel dispatch applies to the direct
entry point above.

Both CPU and CUDA kernels return an input-owned descriptor. Shapes and strides
are marshaled alongside the data. A rank-changing result transfers the same
storage into its new descriptor. Kernels cannot return newly allocated arrays
through this interface.

### Lazy CPU/GPU copies

Owned array storage retains its CUDA allocation between calls. The first GPU
use uploads its elements; subsequent GPU calls in the same context reuse that
allocation. GPU updates make the host elements stale. A host read or CPU kernel
downloads the current contents when needed. Host writes invalidate the device
copy, which is refreshed before the next GPU use. A full host `fill` overwrites
the elements without downloading the old contents. CPU kernels that leave the
contents unchanged do not force a new upload.

[`lazy_copy.ae`](../examples/llvm/gpu/lazy_copy.ae) fills the same matrix in two
GPU calls, then reads an element on the host. It performs one element upload
and one download, and prints `42`:

```bash
python -m aeon examples/llvm/gpu/lazy_copy.ae
```

Reshapes change only metadata and preserve the allocation. The examples'
`snapshot` helpers now transfer ownership into read-only handles that retain
the device storage, so their next GPU call can read it without a download.
Shape, bounds-error, and scalar-result checks still synchronize each kernel;
lazy copying concerns element storage rather than asynchronous execution.

Ordinary Aeon `Array` values are automatically managed at the first GPU call
and remain list-compatible for host indexing, iteration, and mutation.
`from_array` and `to_array` preserve this managed storage across NDArray
conversions. Low-level Python calls that pass plain lists retain eager copying
for compatibility. Exporting an NDArray's raw plain-list `.data` also enables
conservative synchronization so retained Python aliases observe GPU changes.
Use `get` for terminal host reads when a raw list reference is unnecessary.

Device buffers are released when storage is discarded or collected. Calling
the CUDA executor's `close()` materializes live arrays and releases their
cached allocations. Moving an array to another CUDA context or element format
also materializes it before creating the new allocation. Failed calls release
their buffers; unavailable device contents cannot silently become stale host
values.

LLVM supports scalar `Int`, `Float`, `Bool`, `Long`, and `Double` elements.
`Float` uses the existing LLVM float32 representation; the explicit `Cuda`
library's float64 API is separate. The runtime representation contains a data
pointer, offset, rank, dimensions, strides, and an error field. This first
implementation permits owned contiguous storage only; slicing and shared views
are not exposed.

Runnable GPU examples:

- [`zero_matrix_2d.ae`](../examples/llvm/gpu/zero_matrix_2d.ae)
- [`zero_volume_3d.ae`](../examples/llvm/gpu/zero_volume_3d.ae)
- [`lazy_copy.ae`](../examples/llvm/gpu/lazy_copy.ae)
- [`nbody.ae`](../examples/llvm/gpu/nbody.ae)
- [`floyd_warshall.ae`](../examples/llvm/gpu/floyd_warshall.ae)

## N-body simulation example

Run the small gravitational simulation with:

```sh
python -m aeon examples/llvm/gpu/nbody.ae
```

The state is an `N × 7` `(NDArray Float Rank2)`. Each row contains
`[x, y, z, vx, vy, vz, mass]`. The example uses units in which the gravitational
constant is one, positive distance softening to handle coincident bodies, and
semi-implicit Euler integration: update velocity from the old positions, then
update position using the new velocity. The default runs 257 bodies for ten
steps and prints the first body's x coordinate, approximately `-1.95109`.
Change the body count and step count in `main` to try other system sizes.

Each step reads the entire old state before replacing it. On the host,
`snapshot` transfers that state into a flat `Vector Float` with only a read
operation exposed. This uses the existing LLVM pointer representation for
repeated reads; owned `NDArray.get2` currently consumes its array. A separately
allocated 2D destination is passed to `nbody_step`. Its `output.map_rows`
callback gives each thread its own row, updated through method calls such as
`row.set1 0 x`, and the entire matrix is returned with its original shape. Shape and
snapshot-length refinements check index bounds and the seven-column layout.
Termination metrics justify the force loop and simulation loop.

The force calculation is direct all-pairs gravity, requiring O(N²) work.
Bodies run in parallel on CUDA: the default uses two blocks, with a partial
final block. Each body sums interactions with all other bodies and writes one
output row. A kernel synchronization completes every step before its output
becomes the next snapshot. CPU fallback processes the same rows sequentially.
Intermediate states stay on the GPU through the read-only snapshot handles.
Only the final host read downloads a state. Each freshly constructed output
matrix is still uploaded once; reusing output buffers and shared-memory tiling
could improve performance further.
The LLVM CUDA path uses a device square-root intrinsic; state and integration
arithmetic use float32. Tests compare the GPU results with a double-precision
CPU reference and verify the actual CUDA launch dimensions and element-copy
counts across consecutive calls.

## Floyd–Warshall shortest paths

```sh
python -m aeon examples/llvm/gpu/floyd_warshall.ae
```

The example accepts a square `(NDArray Float Rank2)` adjacency matrix for a
directed graph. Positive infinity represents a missing edge. The host
normalizes the diagonal to `min(weight, 0)` to include empty self paths,
rejects NaN and negative infinity, and checks the final diagonal for negative
cycles. Negative edge weights are supported; a negative cycle raises
`ValueError` because finite shortest paths do not exist for that graph.

For each intermediate vertex `k`, `floyd_pass` computes:

```text
next[i, j] = min(previous[i, j], previous[i, k] + previous[k, j])
```

It uses `output.map_rows` to launch one CUDA thread per row, in blocks of 256.
Each thread processes its columns sequentially. The previous matrix is a
read-only snapshot, and threads write disjoint rows of a separate destination.
The host loop synchronizes each pass before advancing to the next pivot;
putting the entire pivot loop inside independent GPU threads would omit this
global barrier. Both arrays remain contiguous, and each GPU pass returns its
supplied output matrix. CPU fallback uses the same recurrence sequentially.

The default four-vertex graph prints `9.0`, the cost of the path `0 → 1 → 2 → 3`.
Tests compare complete distance matrices against repeated Bellman–Ford, check
unreachable vertices and negative cycles, and exercise 257 rows across two
CUDA blocks. Computation is O(N³), with one GPU launch per pivot. Intermediate
matrices remain in device storage, and the final negative-cycle check
materializes the result once. Each fresh host-created destination is still
uploaded once. Buffer lifetime follows live array and snapshot handles; the
host loop can retain prior snapshots until its recursive calls return.
Distance arithmetic uses float32.
The square matrix must fit the NDArray element limit (`0 <= N <= 46340`).
Its `N * N` shape refinements currently trigger nonlinear-arithmetic warnings
from the compiler's decidability scan; the example's type and bounds checks
pass.
