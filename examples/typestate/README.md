# Typestate bugs from Aldrich's papers

This is an executable, attributed suite of **27 Aeon clients**: 19 deliberately
buggy clients and 8 corrected controls. Six controls execute actual Aeon model
operations; two check ownership-polymorphic interfaces without allocating a
resource. Python is only the test harness. The model implementations and clients
contain no axioms, trusted foreign bodies, uninterpreted proof helpers, or holes.

## Sources and adaptations

| Paper | Location | Aeon model / bug classes |
| --- | --- | --- |
| Aldrich, Sunshine, Saini, Sparks, [Typestate-Oriented Programming](https://www.cs.cmu.edu/~aldrich/papers/onward2009-state.pdf), Onward 2009 | Listings 1–2, §§3.1–3.3 | `PlaidFile`: read before opening, read after closing, missing required final close, double close |
| Same paper | Listings 4–5, §3.8 | `PlaidIterator`: missing availability test, advancing an exhausted iterator |
| Same paper | Listing 6, §4 | `PlaidInteractor`: run/stop while idle; a handler that stops despite promising to remain running |
| Same paper | Listing 3, §3.7 | `OwnedAssets`: reuse after ownership transfer to a collection |
| Bierhoff, Beckman, Aldrich, [Checking Concurrent Typestate with Access Permissions in Plural: A Retrospective](https://www.cs.cmu.edu/~aldrich/papers/bierhoff-plural-festschrift11.pdf), 2011 | Figures 1–3, §3.2 | `PluralQueue`: enqueue while closing, dequeue while closed, stale state check across a possible intervening close |
| Coblenz et al., including Aldrich, [Obsidian: Typestate and Assets for Safer Blockchain Programming](https://arxiv.org/pdf/1909.03523), TOPLAS 2020 | Figure 1, §4.1 | `ObsidianVending`: buy while empty, restock while full, omitted Full→Empty transition; `OwnedAssets`: lost or duplicated payment |

These are independently written Aeon adaptations, not copied Plaid/Java/Obsidian
programs or a reproduction of a paper's evaluation dataset. The
[manifest](manifest.json) distinguishes paper-described mistakes from additional
derived mutations and pairs every negative case with a passing control.

## How detection works

The state-machine models are concrete immutable ADTs with constructor equations
for their state measures. Every transition has a checked Aeon implementation.
Calls require the correct input state; functions must establish their declared
output state. For instance:

```aeon
open PlaidFile

# Rejected: create returns a closed file, but read_file requires phase = 1.
def main (u:Int) : Int := read_file (create 42);
```

The corrected file client opens, reads, and returns a closed file. Its runtime
control returns 42. The iterator control tests availability; the interactor
handler preserves Running; the vending control returns a balance of one.

The ownership examples use opaque `linear type Coin` / `FileCapability` and
pure multiplicity-1 transfers. Dropping a parameter gives `LinearUnusedError`,
using it twice gives `LinearUsedTooManyTimesError`, and omitting its `1` binder
gives `LinearTypeNotBoundLinearlyError`. There is no asset factory or assumed
implementation hiding these checks. These two positive controls are compile-only.

## Reproduce

From the repository root:

```bash
pytest tests/aldrich_typestate_test.py -q
AEONPATH=examples/typestate python -m aeon examples/typestate/positive/file_lifecycle.ae
AEONPATH=examples/typestate python -m aeon --no-main examples/typestate/negative/file_read_closed.ae
AEONPATH=examples/typestate python -m aeon --no-main examples/typestate/negative/coin_loss.ae
```

The last two commands intentionally exit with a type-checking error. Tests assert
the diagnostic class and client source file, rather than accepting any failure.
Fresh temporary module paths prevent old compiled caches from masking a defect.

## Boundaries

These models are not filesystem I/O, GUI widgets, a shared heap, a real concurrent
queue, or deployed smart contracts. Their ADTs are unrestricted immutable values;
they do **not** confer unique ownership of a physical file or machine. The linear
ownership interfaces demonstrate a separate guarantee, not Plural's split/merge
permissions, shared alias guarantees, or Obsidian's complete ownership modes.

The queue's `may_close` explicitly represents an intervening transition. Checking
the old queue and then dequeuing the returned queue is rejected. The passing
control checks the returned queue, with no further interference in this model.
This is **not** a proof that rechecking without a lock fixes the paper's real
concurrency bug: the paper's synchronized solution requires a stable permission
or critical section. Aeon is not analyzing thread interleavings here.
