# Typestate case studies from Jonathan Aldrich's papers

The [example suite](https://github.com/alcides/aeon/tree/master/examples/typestate)
contains 19 rejected clients and 8 corrected controls adapted from the Plaid,
Plural, and Obsidian papers. Its
[README](https://github.com/alcides/aeon/blob/master/examples/typestate/README.md)
links the primary papers and maps cases to specific listings and figures.

Aeon detects wrong-state operations and incorrect final states through checked
ADT refinements. Multiplicity-1 ownership interfaces also reject lost, duplicated,
and accidentally unrestricted resources. Six corrected state-machine clients
execute; the two opaque ownership clients are compile-only. All implementations
are Aeon code, without new proof assumptions or foreign implementation bodies.

Run the demonstration and its negative controls:

```bash
pytest tests/aldrich_typestate_test.py -q
```

The tests require the intended refinement or linearity diagnostic at the buggy
client's source location, and compile a corrected counterpart for every bug.
They also reject holes or trusted bodies anywhere in the suite.

These are immutable state-machine and explicit-interference models, not a claim
that Aeon implements Plural's concurrent permissions or Obsidian's smart-contract
runtime. In particular, the queue example models a possible close between two
operations; its passing recheck is not a replacement for synchronization in a
real concurrent program. See the example README's boundaries section.
