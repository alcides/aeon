# Source attribution

The generated programs translate benchmark specifications published with the
research projects linked in [README.md](README.md). Each file identifies its
upstream path. `manifest.json` preserves per-file hashes, and
[`sources.json`](../../scripts/paper_benchmarks/sources.json) pins the exact
archives/commits. Translation code and the added Aeon libraries are part of Aeon.

Available project license notices are reproduced below (terminal blank lines
are normalized by the repository's formatting hooks):

* [Smyth](licenses/smyth.txt), University of Chicago programming languages group.
* [DreamCoder](licenses/dreamcoder.txt), Kevin Ellis and contributors.
* [Hoogle+](licenses/hoogle.txt), TyGuS contributors.
* [Hectare/ECTA](licenses/hectare.txt), James Koppel and contributors.

Other source artifacts did not provide a top-level license file in the inspected
benchmark source tree. Their absence is not a declaration that those sources
are public domain or covered by Aeon's license. Third-party licenses found only
inside unrelated bundled dependencies (such as Burst's Synquid/Leon copies)
are not attributed to the benchmark authors.

Para is taken from the public `nicolas-abril/para-artifact` mirror at the commit
recorded in `sources.json`; it is attributed to Qiantan Hong and Alex Aiken's
*Recursive Program Synthesis using Paramorphisms*. Its regenerated examples
are explicitly distinguished from the paper's unavailable saved examples.

The official SynMem and Trio JFP artifacts are retrieved through their Zenodo
records. No container image, VM, upstream executable, or unrelated dependency
is distributed in this repository. ASAC's original large test corpus is
downloaded and converted locally; its data is not committed.
