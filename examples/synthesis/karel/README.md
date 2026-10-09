# Karel benchmark

This is a reproducible port of the synthesis-token DSL from
[`carpedm20/karel`](https://github.com/carpedm20/karel), the generator used by
the Karel program-synthesis datasets.  Aeon's dependency-free interpreter is
`aeon.benchmarks.karel`; it accepts source programs such as:

```text
DEF run m( WHILE c( frontIsClear c) w( move w) m)
```

Use `generate_examples(program, seed, count)` to create deterministic Karel
input/output tasks for a synthesis backend. The implementation covers actions,
conditions, `IF`, `IFELSE`, `WHILE`, and `REPEAT`, with a bounded evaluator to
make non-terminating candidates safe to score.
