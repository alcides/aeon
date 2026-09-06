# Typestate protocols from LiquidJava, in Aeon

Four small libraries port the LiquidJava demos that fit Aeon best: a mutex,
a streaming reader, a fluent email builder, and a download session with a
progress ghost. Each combines **linear handles** (use exactly once) with
**refinement measures** (legal orderings / numeric bounds). ``Stack`` and
``Deque`` add size-ghost collection protocols.

| Module | LiquidJava analogue | Idea |
|--------|---------------------|------|
| [`Lock`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Lock.ae) | `ReentrantLock` | unlocked ↔ locked; destroy only when free |
| [`Reader`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Reader.ae) | `InputStreamReader` | open → read* → close; byte codes in `[-1, 255]` |
| [`Email`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Email.ae) | fluent `Email` | from → to+ → body → build |
| [`Downloader`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Downloader.ae) | `Downloader` | start → monotonic update → finish at 100% |
| [`Stack`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Stack.ae) | `Stack` | push/pop/peek with `size` ghost |
| [`Deque`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Deque.ae) | `ArrayDeque` | dual-ended push/pop/peek with `size` |

Examples (typecheck with `--no-main`):
[`lock_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/lock_example.ae),
[`reader_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/reader_example.ae),
[`email_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/email_example.ae),
[`downloader_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/downloader_example.ae),
[`stack_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/stack_example.ae),
[`deque_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/deque_example.ae).

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

## Stack

```aeon
open Stack

def demo (u: Unit) : Int :=
    let 1 s0 := new_stack{Int} u in
    let 1 s1 := push 7 s0 in
    let po := pop s1 in
    let v := pop_value po in
    let 1 s2 := pop_stack po in
    let _ := discard s2 in
    v;
```

`pop` / `peek` require `stack_size > 0`; `discard` requires an empty stack.

## Deque

```aeon
open Deque

def demo (u: Unit) : Int :=
    let 1 d0 := new_deque{Int} u in
    let 1 d1 := push_back 1 d0 in
    let 1 d2 := push_front 0 d1 in
    let po := pop_front d2 in
    let v := pop_value po in
    let 1 d3 := pop_deque po in
    let po2 := pop_back d3 in
    let _ := pop_value po2 in
    let 1 d4 := pop_deque po2 in
    let _ := discard d4 in
    v;
```

Same size discipline as `Stack`, with operations at both ends.

---

## Related reading

- [State-safe `Database`](database.md) — Conn/Txn typestate
- [Linear `Socket`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Socket.ae) — bind/connect/close
- [LiquidJava examples](https://github.com/liquid-java/liquidjava-examples) — original Java demos
