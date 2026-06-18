# Matrix / tensor transformation benchmarks (BLAZE / SYNGAR)

These `.ae` files are the **matrix domain** of Wang, Dillig & Singh,
*Program Synthesis using Abstraction Refinement* (POPL'18, arXiv:1710.07740) —
the second domain BLAZE was instantiated for (Fig.17 DSL: `Reshape`, `Permute`,
`Fliplr`, `Flipud`). They are solved by the AFTA backend's example-driven (PBE)
mode:

```bash
uv run python -m aeon --no-main -s afta --budget 60 examples/synthesis/afta/matrix/<file>.ae
```

## Matrix encoding

A matrix is encoded as a **MATLAB-style string** — rows separated by `;`,
elements by `,` — exactly the notation the paper uses (the running example
reshapes the vector `[1,2,3,4,5,6]` row-wise into `1,2,3;4,5,6`). Encoding
matrices as strings lets the existing PBE engine and the `@example` I/O
specification work unchanged; the Fig.17 operators live in
[`libraries/Matrix.ae`](../../../../libraries/Matrix.ae) as total `String ->
String` (plus `Int` size args) functions.

## On the benchmark count

The paper's 39 matrix benchmarks were scraped from StackOverflow / MathWorks
forum posts and are **not individually published** in the paper. What the paper
*does* give is the DSL (Fig.17) and the running reshape example. The files here
are therefore a faithful **reconstruction** that exercises every Fig.17 operator
and representative compositions:

- single operators: `reshape_2x3`, `reshape_3x2`, `transpose`, `fliplr`,
  `flipud`, `flatten`, `reverse_vector`
- compositions: `reshape_then_flipud`, `reshape_then_transpose`, `rotate180`

To synthesise against a different forum task, add an `.ae` with its `@example`
input/output pair(s) in the string encoding above.
