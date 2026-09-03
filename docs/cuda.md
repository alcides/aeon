# `Cuda`: explicit GPU buffers with linear types and refinements

`Cuda.ae` wraps the CUDA Driver API for **explicit** device memory: upload host
arrays, launch fixed elementwise kernels, synchronize, download snapshots, and
free allocations. It is **not** imported by the `@gpu` decorator — that path uses
[`Gpu`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Gpu.ae) and
tensors. Use `Cuda` when you want compile-time proofs about devices, sizes, and
byte budgets.

- Source: [`aeon/libraries/Cuda.ae`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Cuda.ae)
- Examples: [`examples/llvm/gpu/`](https://github.com/alcides/aeon/tree/master/examples/llvm/gpu)
- Generated reference: [stdlib/Cuda.html](stdlib/Cuda.html) (from `aeon --doc`)

---

## Resource lifecycle

Every host array and GPU handle is **linear** (`let 1`, parameter `(1 …)`): each
value is consumed exactly once. The typical Int vector-add path:

```
Array ──upload──► ReadyBuffer ──add──► Pending ──synchronize──► ReadyBuffer
                      │                                              │
                      └──────────────── download ──► I32Download ──unpack──► Array + ReadyBuffer
                                                                                    │
                                                                                 free ──► Unit
```

| Handle | Role |
|--------|------|
| `Device` | Immutable CUDA device descriptor |
| `Launch1D` | 1-D grid: item count, block size, derived grid coverage |
| `Stream` | CUDA stream for ordered kernel enqueue |
| `ReadyBuffer a` | Device allocation ready for kernels or download |
| `Pending a` | In-flight kernel result (must `synchronize` or `discard`) |
| `I32Download` / `Float64Download` | Linear token: host snapshot + preserved buffer |
| `*DownloadPair` | Unrestricted pair projected after `unpack_*` |

`discard` abandons a `Pending` without reading results. `free` releases a
`ReadyBuffer`.

---

## Refinement guarantees

The bindings prove (at compile time):

- **Device bounds** — `device id` is in `[0, num_devices)`; `num_devices > 0`.
- **Launch validity** — block size ≤ item count, ≤ hardware `max_threads_per_block`, grid covers all items.
- **Size matching** — binary kernels require equal non-empty buffers on the launch device, sized to `launch_items`.
- **Byte budget** — `buffer_bytes = size × elem_size` (4 for `Int`, 8 for `Float`) ≤ `max_allocation device`.
- **Dtype indexing** — `buffer_elem_size` is 4 or 8 for the supported upload/kernel paths.

Violations are type errors, not runtime surprises.

---

## Supported operations

| Category | Functions |
|----------|-----------|
| Discovery | `num_devices`, `device`, `default_device`, `default_stream` |
| Launch | `launch_1d` |
| Host → device | `upload_i32`, `upload_float64` |
| Kernels | `add_i32`, `add_float64` (elementwise vector add) |
| Sync | `synchronize`, `discard` |
| Device → host | `download_i32`, `download_float64`, `unpack_*`, `download_values_*`, `download_buffer_*` |
| Release | `free` |

Aeon's surface `Float` maps to **CUDA float64** in this module; there is no silent
float32 narrowing.

---

## Minimal example

```aeon
import Array;
import Cuda;

open Cuda

def vector_add (u: Unit) : Int :=
    let d := default_device u in
    let stream := default_stream d in
    let launch := launch_1d d 3 1 in
    let 1 xs := Array.append (Array.append (Array.append (Array.new{Int} u) 11) 22) 33 in
    let 1 ys := Array.append (Array.append (Array.append (Array.new{Int} u) 1) 2) 3 in
    let 1 left := upload_i32 d xs in
    let 1 right := upload_i32 d ys in
    let 1 pending := add_i32 launch stream left right in
    let 1 ready := synchronize pending in
    let 1 downloaded := download_i32 ready in
    let pair := unpack_i32_download downloaded in
    let 1 result := download_values_i32 pair in
    let 1 buf := download_buffer_i32 pair in
    let total := Array.sum result in
    let _ := free buf in
    total;
```

Requires a CUDA-capable GPU and driver at runtime. See
[`examples/llvm/gpu/cuda_vector_add.ae`](https://github.com/alcides/aeon/blob/master/examples/llvm/gpu/cuda_vector_add.ae).

---

## Related reading

- [Linear `Array` buffers](array.md) — multiplicity-1 host arrays consumed by `upload_*`
- [State-safe `Database`](database.md) — another linear-resource case study
- [Writing FFI bindings](ffi) — how measures and `native` bodies stay honest
