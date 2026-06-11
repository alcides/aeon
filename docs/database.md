# `Database`: state-safe sqlite3 with linear types and refinements

`Database.ae` wraps Python's `sqlite3` so the two things that make raw database
code error-prone — **transaction discipline** and **connection state** — are
checked by the compiler. It is the standard library's flagship example of
combining Aeon's two big ideas: [Liquid Types](index.md) for the *values* and
**Quantitative Type Theory** (linear/multiplicity types, as in
[`Socket.ae`](https://github.com/alcides/aeon/blob/master/libraries/Socket.ae))
for the *protocol*.

- Source: [`libraries/Database.ae`](https://github.com/alcides/aeon/blob/master/libraries/Database.ae)
- Example: [`examples/imports/database_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/database_example.ae)

---

## The two failure modes

```python
conn = sqlite3.connect("app.db")
conn.execute("INSERT INTO log VALUES ('x')")
# ... forgot conn.commit() — the write silently vanishes
conn.close()
conn.execute("SELECT ...")   # ProgrammingError: closed database
```

1. **Transaction discipline.** A transaction must be committed *xor* rolled
   back — **exactly once** — and the connection closed **exactly once**. Forget
   the commit and your writes disappear; touch the connection after close and
   you crash. These are *linear-resource* rules.
2. **State.** `execute` only makes sense inside an open connection; `commit`
   only inside a transaction. Doing things out of order is a state error.

A `with` block guards a single scope, but it cannot express "you owe exactly one
of commit-or-rollback on this handle, and may not touch it afterward." Linear
types can.

## Typestate: the handle's *kind* is the state

`Database` exposes two opaque handle types, and the operations move between them:

```aeon
type Conn      # an open connection        (linear)
type Txn       # a connection inside a txn  (linear)

def connect  (path: {p:String | p != ""}) : Conn          # → Conn
def begin    (1 c: Conn)                    : Txn          # Conn → Txn
def execute  (sql: {s:String | s != ""}) (1 t: Txn) : Txn  # Txn  → Txn
def commit   (1 t: Txn)                     : Conn         # Txn  → Conn
def rollback (1 t: Txn)                     : Conn         # Txn  → Conn
def close    (1 c: Conn)                    : Unit         # Conn → ∎
```

Because the states are *distinct types*, illegal orderings simply don't
type-check: you cannot `execute` on a `Conn` (you must `begin` first), nor
`close` a `Txn` (you must `commit`/`rollback` first). Closing a transaction is a
plain type error:

```
Expression has type Txn, but is expected to have type Conn
```

## Linearity: exactly once, in order

The `(1 c: …)` annotation marks a parameter consumed at **multiplicity 1**, and
results are bound with `let 1`. Each operation consumes its handle and returns
the next state, so the whole lifecycle threads through linear binders — exactly
like `Socket.ae`:

```aeon
def writeEntry (path: {p:String | p != ""}) : Unit :=
    let 1 c0 := Database.connect path in
    let 1 t0 := Database.begin c0 in
    let 1 t1 := Database.execute "CREATE TABLE IF NOT EXISTS log (msg TEXT)" t0 in
    let 1 t2 := Database.execute "INSERT INTO log VALUES ('entry')" t1 in
    let 1 c1 := Database.commit t2 in       # MUST commit or rollback — exactly once
    Database.close c1;                      # MUST close — c0/t0/t1 are now spent
```

The type checker now rejects every classic mistake:

| Mistake | Error |
|---|---|
| Forget `commit`/`rollback` (writes lost) | `Linear binding t2 … is never used` (`LinearUnusedError`) |
| Forget `close` (leaked connection) | `Linear binding c1 … is never used` |
| `commit` twice / use a spent txn | `Linear binding t2 … is used 2 times` (`LinearUsedTooManyTimesError`) |
| `execute` after `commit` | the old `Txn` binder was already consumed → over-use error |
| `close` a `Txn` | type mismatch `Txn` vs `Conn` |

A correct, complete lifecycle is the *only* thing that type-checks.

## Reads need no ceremony

A `SELECT` that needs no transaction uses the non-linear one-shot path, which
opens and closes the connection internally (so nothing can leak), with ordinary
refinements on the result:

```aeon
def row_count : (r: Rows) -> Int := uninterpreted

def read_all (path: {p:String | p != ""}) (sql: {s:String | s != ""}) :
    {r: Rows | row_count r >= 0} := ...

def num_rows (r: Rows) : {n:Int | n = row_count r && n >= 0} := native "len(r)"
def is_empty (r: Rows) : {b:Bool | b = (row_count r = 0)} := native "len(r) == 0"
```

```aeon
def count_rows (path: {p:String | p != ""}) : Int :=
    Database.num_rows (Database.read_all path "SELECT * FROM log");
```

## A note on the trust boundary

As with any FFI binding, the refinements and the state machine are **promises
the wrapper makes** (see [the FFI guide](ffi#mental-model)). They are honest
here: `connect(..., isolation_level=None)` puts sqlite3 in autocommit so the
explicit `BEGIN`/`COMMIT`/`ROLLBACK` are obeyed verbatim, and each linear
operation maps to exactly one underlying call. Keep that correspondence intact
if you extend the module.
