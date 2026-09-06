# `Cuda`: explicit GPU buffers with linear types and refinements

`Cuda.ae` wraps the CUDA Driver API for **explicit** device memory: upload host
arrays, launch fixed elementwise kernels, synchronize, download snapshots, and
free allocations. It is **not** imported by the `@gpu` decorator — that path uses
[`Gpu`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Gpu.ae) and
tensors. Use `Cuda` when you want compile-time proofs about devices, sizes, byte
budgets, memory kind, access mode, launch shape, shared/warp legality, and
optional Status-aware sync.

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
| `Launch1D` / `Launch2D` | Grid descriptors (1-D items/threads; 2-D width×height + block dims) |
| `Stream` | CUDA stream for ordered kernel enqueue |
| `ReadyBuffer a` | Device allocation ready for kernels or download |
| `Pending a` | In-flight kernel result (must `synchronize` or `discard`) |
| `Status` / `StatusBuffer a` | Optional sync-with-status path (`check_ok` / `discard_status`) |
| `I32Download` / `Float64Download` | Linear token: host snapshot + preserved buffer |
| `*DownloadPair` / `StatusPair` | Unrestricted pairs after unpack |

`discard` abandons a `Pending` without reading results. `free` releases a
`ReadyBuffer`. The main lifecycle above is unchanged; Status and read-only views
are parallel APIs.

---

## Refinement guarantees

The bindings prove (at compile time):

- **Device bounds** — `device id` is in `[0, num_devices)`; `num_devices > 0`.
  Device posts also fix CUDA lower bounds: `max_threads_per_block ≥ 1024`,
  `warp_size = 32`, `max_shared_mem_per_block ≥ 0`.
- **Launch validity** — block size ≤ item count, ≤ `max_threads_per_block`, ≤ 1024;
  grid covers all items (1-D) or width×height (2-D).
- **Size matching** — binary kernels require equal non-empty buffers on the launch device, sized to `launch_items`.
- **Byte budget** — `buffer_bytes = size × elem_size` (4 for `Int`, 8 for `Float`) ≤ `max_allocation device`.
- **Dtype indexing** — `buffer_elem_size` is 4 or 8 for the supported upload/kernel paths.
- **Memory kind** — uploads tag `buffer_mem_kind = mem_kind_device`; kernels require device kind on both inputs. Host/pinned/managed constants are reserved for future allocators.
- **Access mode** — uploads and sync outputs are read-write; `as_read_only` freezes a buffer to RO while preserving device/size/kind/extents; kernels accept RO or RW inputs.
- **Shape / extents** — 1-D uploads set `extent_x = size`, `extent_y = 1`; `Launch2D` proves grid coverage of width×height (`tx×ty ≤ 1024` and ≤ device limit). No 2-D kernels yet—descriptors prepare for them.
- **Shared memory** — `launch_1d_shared` / `launch_2d_shared` record `0 ≤ shared ≤ max_shared_mem_per_block`; plain `launch_1d` keeps `shared_bytes = 0`.
- **Warp legality** — `launch_1d_warped` additionally requires `threads ≤ warp_size ∨ threads % warp_size = 0`.
- **Status** — `synchronize_with_status` yields a linear `StatusBuffer`; unpack then `check_ok` (refined-ok) or `discard_status`. Unused Status is a linearity error.

Violations are type errors, not runtime surprises.

---

## Supported operations

| Category | Functions |
|----------|-----------|
| Discovery | `num_devices`, `device`, `default_device`, `default_stream` |
| Launch | `launch_1d`, `launch_1d_shared`, `launch_1d_warped`, `launch_2d`, `launch_2d_shared` |
| Host → device | `upload_i32`, `upload_float64` |
| Access | `as_read_only` |
| Kernels | `add_i32`, `add_float64` (elementwise vector add) |
| Sync | `synchronize`, `synchronize_with_status`, `discard` |
| Status | `unpack_status_buffer`, `status_pair_*`, `check_ok`, `discard_status` |
| Device → host | `download_i32`, `download_float64`, `unpack_*`, `download_values_*`, `download_buffer_*` |
| Release | `free` |

Aeon's surface `Float` maps to **CUDA float64** in this module; there is no silent
float32 narrowing.

### Parallel APIs (optional)

Read-only view before a kernel (both inputs may be RO):

```aeon
let 1 left := as_read_only left0 in
let 1 right := as_read_only right0 in
let 1 pending := add_i32 launch stream left right in
```

Shared / warp-aware / 2-D launch descriptors (kernels still use 1-D `Launch1D` today):

```aeon
let l1 := launch_1d_shared d 8 4 0 in
let lw := launch_1d_warped d 64 32 in
let l2 := launch_2d d 33 17 16 8 in
```

Status-aware sync (must consume Status linearly):

```aeon
let 1 sb := synchronize_with_status pending in
let pair := unpack_status_buffer sb in
let 1 st := status_pair_status pair in
let 1 buf := status_pair_buffer pair in
let _ := check_ok st in
```

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
