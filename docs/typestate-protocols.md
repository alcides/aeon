# Typestate protocols from LiquidJava, in Aeon

Four small libraries port the LiquidJava demos that fit Aeon best: a mutex,
a streaming reader, a fluent email builder, and a download session with a
progress ghost. Each combines **linear handles** (use exactly once) with
**refinement measures** (legal orderings / numeric bounds).

| Module | LiquidJava analogue | Idea |
|--------|---------------------|------|
| [`Lock`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Lock.ae) | `ReentrantLock` | unlocked ↔ locked; destroy only when free |
| [`Reader`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Reader.ae) | `InputStreamReader` | open → read* → close; byte codes in `[-1, 255]` |
| [`Email`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Email.ae) | fluent `Email` | from → to+ → body → build |
| [`Downloader`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Downloader.ae) | `Downloader` | start → monotonic update → finish at 100% |

Examples (typecheck with `--no-main`):
[`lock_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/lock_example.ae),
[`reader_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/reader_example.ae),
[`email_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/email_example.ae),
[`downloader_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/downloader_example.ae).

---

## Lock

```aeon
open Lock

def critical (u: Unit) : Unit :=
    let 1 l0 := new_lock u in
    let 1 l1 := acquire l0 in
    let 1 l2 := release l1 in
    destroy l2;
```

`acquire` requires `lock_held = false`; `release` / `destroy` require the
matching state. Leaking or double-acquiring a held lock is rejected.

## Reader

```aeon
open Reader

def read_once (path: {p: String | p != ""}) : Int :=
    let 1 r0 := open_reader path in
    let step := read r0 in
    let code := read_code step in
    let 1 r1 := read_reader step in
    let _ := close r1 in
    code;
```

Unlike one-shot `Path.read`, the linear `Reader` must be closed. Each `read`
returns a `ReaderStep` (code + recovered open handle).

## Email

```aeon
open Email

def compose (u: Unit) : String :=
    let 1 e0 := new_email u in
    let 1 e1 := set_from "alice@example.com" e0 in
    let 1 e2 := add_to "bob@example.com" e1 in
    let 1 e3 := set_body "Hi Bob," e2 in
    build e3;
```

`email_phase` enforces the builder order. Building before `set_body`, or
setting the sender twice, does not type-check.

## Downloader

```aeon
open Downloader

def download (u: Unit) : Unit :=
    let 1 d0 := new_downloader u in
    let 1 d1 := start d0 in
    let 1 d2 := update d1 40 in
    let 1 d3 := update d2 100 in
    let 1 d4 := finish d3 in
    discard d4;
```

Updates must strictly increase `progress`; `finish` requires `progress = 100`.

---

## Related reading

- [State-safe `Database`](database.md) — Conn/Txn typestate
- [Linear `Socket`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Socket.ae) — bind/connect/close
- [LiquidJava examples](https://github.com/liquid-java/liquidjava-examples) — original Java demos
