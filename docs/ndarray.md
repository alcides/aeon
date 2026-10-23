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
The array planner also schedules composed fills in parallel; arbitrary scalar
functions retain their normal execution. Launch dimensions are separate
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
callback and writes their results back. Array operations composed in a GPU entry
are scheduled as parallel stages by the array plan described below.

Both CPU and CUDA kernels return an input-owned descriptor. Shapes and strides
are marshaled alongside the data. A rank-changing result transfers the same
storage into its new descriptor. For operations that change element type or output size, the array planner supplies
a managed destination parameter. Its allocation can stay on the device.

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

Reshapes change only metadata and preserve the allocation. Array-valued map,
zip, scan, axis reduction, fill, and row-map entries enqueue work on the default
CUDA stream. Their next GPU call can use the result without waiting on the host.
A host element read, CPU use, scalar result, or dynamic filter length synchronizes
when that value is needed. Deferred bounds and driver errors are reported at that
boundary; failed outputs cannot be read as stale host values.

Ordinary Aeon `Array` values are automatically managed at the first GPU call
and remain list-compatible for host indexing, iteration, and mutation.
`from_array` and `to_array` preserve this managed storage across NDArray
conversions. Low-level Python calls that pass plain lists retain eager copying
for compatibility. Exporting an NDArray's raw plain-list `.data` also enables
conservative synchronization so retained Python aliases observe GPU changes.
Use `get` for terminal host reads when a raw list reference is unnecessary.

Reusable allocations return to a pool when storage is discarded or collected. Calling
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
- [`reductions.ae`](../examples/llvm/gpu/reductions.ae)
- [`filter.ae`](../examples/llvm/gpu/filter.ae)
- [`array_pipeline.ae`](../examples/llvm/gpu/array_pipeline.ae)
- [`nbody.ae`](../examples/llvm/gpu/nbody.ae)
- [`floyd_warshall.ae`](../examples/llvm/gpu/floyd_warshall.ae)

### Parallel scalar reductions

`reduce` consumes an NDArray of any rank and combines its row-major elements
with a lambda. Sum, minimum, and maximum use the same compiler operation:

```aeon
@gpu
def sum_values (1 values:(NDArray Int Rank1)) : Int :=
    values.reduce (fun acc => fun x => acc + x) 0;

@gpu
def min_values (1 values:(NDArray Int Rank1)) : Int :=
    values.reduce (fun acc => fun x => if acc < x then acc else x) 2147483647;

@gpu
def max_values (1 values:(NDArray Int Rank1)) : Int :=
    values.reduce (fun acc => fun x => if acc > x then acc else x) (-2147483647 - 1);
```

The lambda goes through normal lowering into `LLVMVectorReduce`; its body uses
the existing expression generator for both CPU and CUDA. It can capture scalar
parameters and call compiled helpers. CUDA combines adjacent elements in a
shared-memory tree with 256 threads per block, then reduces device-resident
partial results until one value remains. Only the final scalar is downloaded;
input arrays already on the GPU stay there.

The initial value is applied exactly once, and is returned unchanged for an
empty array. The combiner must be pure and associative. Element order is
preserved, but grouping changes, so floating-point sums can differ from the
sequential interpreter/CPU fold through rounding. This property is the
caller's contract and is not proved by the typechecker.

Homogeneous scalar reductions use parallel stages, both as direct entries and
in composed array plans. Existing `reduce_n_int` and `reduce_n_float` calls with
an input parameter and parameter/literal length use this same path. General
folds with different accumulator and element types retain sequential lowering.
Compiled scalars include `Int`, `Long`, `Float`, `Double`, and `Bool`.

Run `python -m aeon examples/llvm/gpu/reductions.ae` to print `524800`, `0`,
and `1024` from three multi-block reductions.

### Parallel stable filtering

`filter` consumes an NDArray and returns its selected elements as a packed
rank-one array, preserving their row-major order:

```aeon
@gpu
def select_even (1 values:(NDArray Int Rank1)) : (NDArray Int Rank1) :=
    values.filter (fun x => x % 2 = 0);
```

The predicate is a normal compiled lambda and can capture scalar parameters
and call compiled helpers. The compiler lowers it to `LLVMVectorFilter`,
using the same expression visitor as reductions. Predicates must be pure.

CUDA evaluates the predicate once per element, scans flags within blocks of
256 threads, scans block totals hierarchically, and scatters survivors to
distinct output positions. This preserves order across blocks without an
atomic append counter. The output allocation transfers to the existing linear
owner; selected elements are not copied back into the old allocation.

The host receives the selected count, alongside descriptor checks. Element
contents remain on the GPU for subsequent filters, reductions, or other GPU
calls. Empty inputs and predicates selecting nothing produce an empty array.
Host reads and CPU kernels materialize the packed prefix through the same lazy
storage path. Low-level plain Python lists retain eager compatibility.

`filter_n_int` and `filter_n_float` in `ArrayKernels` use the same GPU path,
selecting from the first `n` elements and returning an array with its actual
runtime length. Both CPU and GPU launch paths validate `n` against the input
length. Direct entries and filters inside an array plan use the parallel path.

Run `python -m aeon examples/llvm/gpu/filter.ae` to filter 1,025 integers and
sum the even survivors in a second GPU call. It prints `262656` without an
intermediate download of the selected elements.

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
Termination metrics justify the force loop; `iterate` bounds the simulation loop.

The force calculation is direct all-pairs gravity, requiring O(N²) work.
Bodies run in parallel on CUDA: the default uses two blocks, with a partial
final block. Each body sums interactions with all other bodies and writes one
output row. Default-stream ordering completes each step before the next kernel
reads it. Two element buffers alternate through `iterate`, and zero initialization
runs on the device. CPU fallback processes the same rows sequentially. Only the
final host read downloads a state. Shared-memory tiling remains a possible
performance improvement.
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
Default-stream ordering supplies the global barrier between pivot launches.
The host can enqueue successive passes without synchronizing each one.
Both arrays remain contiguous, and each GPU pass returns its
supplied output matrix. CPU fallback uses the same recurrence sequentially.

The default four-vertex graph prints `9.0`, the cost of the path `0 → 1 → 2 → 3`.
Tests compare complete distance matrices against repeated Bellman–Ford, check
unreachable vertices and negative cycles, and exercise 257 rows across two
CUDA blocks. Computation is O(N³), with one GPU launch per pivot. Intermediate
matrices remain in device storage, and the final negative-cycle check
materializes the result once. `iterate` reuses two device buffers and supplies
scoped read-only source views; the destination is zeroed on the GPU between uses.
Distance arithmetic uses float32.
The square matrix must fit the NDArray element limit (`0 <= N <= 46340`).
Its `N * N` shape refinements currently trigger nonlinear-arithmetic warnings
from the compiler's decidability scan; the example's type and bounds checks
pass.

### Composing array operations

A GPU entry may contain nested array expressions, `let` bindings, calls to
nonrecursive array helpers, and conditionals. The compiler builds a plan after
ordinary LLVM lowering. Each collective becomes a compiled stage, so a
`map → filter → reduce` expression uses parallel CUDA operations throughout.
Scalar helpers and lambdas continue through the shared expression generator.
A branch condition that depends on a GPU scalar waits for that scalar. Recursive
array pipelines should use a host loop or `iterate`; recursion within ordinary
scalar device helpers remains supported.

```aeon
@gpu
def selected_sum (1 xs:(NDArray Int Rank2)) : Int :=
    let 1 shifted := xs.map (fun x => x + 1) in
    let 1 scaled := shifted.map (fun x => x * 2) in
    let 1 selected := scaled.filter (fun x => x > 10) in
    selected.reduce (fun acc => fun x => acc + x) 0;
```

Consecutive maps, and a map following `zipWith`, fuse into one elementwise
kernel. Intermediate scalar conversions are retained. Fusion currently applies
within an entry, not across separate function invocations; reductions, scans,
and filters remain distinct stages. The CPU backend executes the same plan
with sequential compiled loops, and the interpreter provides matching methods.

| Method | Result |
| --- | --- |
| `xs.map f` | Apply `f` to every element, preserving shape; element type may change. |
| `xs.zipWith ys f` | Combine matching elements of identically shaped arrays. |
| `xs.reduce_axis axis f z` | Reduce one axis, keeping that dimension with size one. |
| `xs.scan f z` | Inclusive row-major prefix folds, preserving shape. |
| `xs.scan_exclusive f z` | Prefix folds excluding the current element; the first result is `z`. |
| `xs.iterate steps value f` | Run a callback over two alternating buffers of the original shape. |

`map` and `zipWith` consume their owned inputs. When shape and element type
permit, the result reuses the first input's allocation. A type change or axis
reduction uses a managed destination allocated without uploading initial elements.
`zipWith` validates full shapes before launching, including zero-sized dimensions.

Axis reductions launch one block per output position, with lanes combining
contiguous chunks of the chosen axis and then reducing in shared memory. Scans
use a hierarchy of block scans and prefix propagation; all passes remain on the
GPU. Both accept the same pure, associative scalar combiners as `reduce`.
Their seed is applied once to each result, and need not be an identity. Empty
axis slices return the seed; a scan of an empty array stays empty. Operand order
is preserved, while parallel grouping can change floating-point rounding.

### Reusing buffers across iterations

`iterate` is a host scheduler for GPU callbacks. It passes the iteration index,
a scoped `ReadOnly` source view, and an owned destination filled with `value`.
The callback must return that destination with the original shape. Two element
allocations alternate across iterations; zero fills are issued on the device.
The examples [N-body](../examples/llvm/gpu/nbody.ae) and
[Floyd–Warshall](../examples/llvm/gpu/floyd_warshall.ae) use this method:

```aeon
state.iterate steps 0.0
    (fun step => fun source => fun output => nbody_step source n dt softening output)
```

Import `ReadOnly` to use `source.read index` in callbacks and `ReadOnly.size source`
in refinements. A borrowed view expires as its callback returns. Keeping a view
in a closure does not keep the borrow valid: a later host access or GPU invocation
through that view raises an error. This allows the next iteration to reuse its
storage without changing any still-valid immutable snapshot.

The runtime keeps up to 64 MiB of reusable device allocations and bounds queued
staging resources by completing batches after 256 submissions/launches. Resource
pressure can therefore introduce a wait before a host read. Descriptor uploads
use pinned staging memory retained until completion. Raw Python list aliases
remain eager for compatibility. `CUDAExecutionEngine.close()` waits, materializes
live results, and frees the pool. Pool ownership is per CUDA context.
