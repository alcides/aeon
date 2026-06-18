# `OS` and `Subprocess`: typed bindings for error-prone system calls

Two of the most bug-prone corners of the Python standard library are `os` and
`subprocess`. Their failure modes are not exotic — they are the everyday
mistakes that ship to production: reading an environment variable that isn't
set, ignoring a non-zero exit code, building a shell command out of string
concatenation. Aeon's [Liquid Types](index.md) are a natural fit here: the
preconditions that *should* hold before each call can be written into the type,
and the SMT solver checks them at compile time instead of letting them surface
as a runtime `KeyError`, `CalledProcessError`, or — worse — a shell injection.

This page covers the two bindings, the specific error classes they rule out,
and how to use them. For the general mechanics of writing such a binding (`native`,
`native_import`, opaque types, uninterpreted measures), see
[Writing FFI bindings for a Python package](ffi).

- Source: [`libraries/OS.ae`](https://github.com/alcides/aeon/blob/master/libraries/OS.ae),
  [`libraries/Subprocess.ae`](https://github.com/alcides/aeon/blob/master/libraries/Subprocess.ae)
- Examples: [`examples/imports/os_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/os_example.ae),
  [`examples/imports/subprocess_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/subprocess_example.ae)

---

## `OS` — partial operations made total

The `os` module is full of calls that look innocent but raise on a bad input.
`OS.ae` attaches refinements so the obvious mistakes don't typecheck.

### Environment access without `KeyError`

`os.environ[k]` raises `KeyError` when `k` is unset — the single most common
`os` bug. `OS.ae` models environment membership with an **uninterpreted
predicate** and gates the unchecked lookup behind it:

```aeon
def envSet : (name: String) -> Bool := uninterpreted

# Runtime witness: in the `then` branch the solver learns `envSet name`.
def hasEnv (name: {s:String | s != ""}) : {b:Bool | b = envSet name} :=
    native "name in os.environ"

# Unchecked lookup — its precondition makes a KeyError unrepresentable.
def getEnv (name: {s:String | s != "" && envSet s}) : String :=
    native "os.environ[name]"
```

`getEnv` is only well-typed where the solver already knows `envSet name`, which
is exactly the refinement that the `then` branch of `if hasEnv name then …`
introduces (the same pattern `Path.ae` uses for `exists`/`read_text`):

```aeon
def homeDir : String :=
    if OS.hasEnv "HOME" then
        OS.getEnv "HOME"      # OK: branch refines `envSet "HOME"`
    else
        "/"
```

Drop the guard and the program is rejected at compile time:

```aeon
def bad : String := OS.getEnv "HOME"
```

```
>>> Type error: Failed to prove ... ((vs != "") && OS_envSet(vs))
```

When you'd rather not branch, `getEnvOr name fallback` is total and always safe.

### Exit codes that fit in a byte

`os._exit` truncates its argument to one byte, so `os._exit(256)` silently
becomes `0` — a "success" exit that wasn't. The refinement pins the value to
the portable range:

```aeon
def exitNow (code: {x:Int | x >= 0 && x <= 255}) : Unit := native "os._exit(code)"
```

### Other guarded calls

| Function | Refinement | Bug it prevents |
|---|---|---|
| `getPid`, `getParentPid` | result `> 0` | downstream "is this a real PID?" checks |
| `cpuCount` | returns `Maybe Int` | dividing by a `None` CPU count |
| `getCwd` | result `!= ""` | empty-path propagation |
| `fileSize` | result `>= 0` | treating an error sentinel as a size |
| `kill pid sig` | `pid > 0 && sig > 0` | signalling PID 0 (the whole process group) |

---

## `Subprocess` — no shell, no ignored failures

`subprocess` is dangerous in two independent ways. `Subprocess.ae` closes both.

### 1. No shell injection — argv only

The classic vulnerability is `subprocess.run("rm " + name, shell=True)`: a
hostile `name` like `"; rm -rf /"` is handed straight to `/bin/sh`. The fix is
to pass an **argument vector** and never invoke a shell — then there is no shell
grammar to inject into. This binding exposes *only* the argv form. Every entry
point takes a non-empty `Array String` (the first element is the program), and
there is deliberately no `shell=True` escape hatch:

```aeon
def run (argv: {a: (Array String) | Array.size a >= 1}) : CompletedProcess :=
    native "subprocess.run(argv, capture_output=True, text=True)"
```

An `Array String` is a Python `list[str]` at runtime, so it flows directly into
`subprocess.run`. The non-empty refinement is discharged for free by `append`'s
`Array.size` postconditions:

```aeon
def echoArgs : {a: (Array String) | Array.size a >= 1} :=
    Array.append (Array.append (Array.new[String]) "echo") "hello"
```

An empty argv — which would raise `IndexError` inside `subprocess` — is a type
error:

```aeon
def bad : CompletedProcess := Subprocess.run (Array.new[String])
```

```
>>> Type error: Failed to prove (Array_size(arr) >= 1)
```

### 2. Exit codes you can't forget

`subprocess.run` does not raise on failure, so it's easy to read the `stdout`
of a command that never succeeded. The binding reflects the return code into an
uninterpreted `exitCode` measure and ties `succeeded` to it:

```aeon
def exitCode : (p: CompletedProcess) -> Int := uninterpreted

def succeeded (p: CompletedProcess) : {b:Bool | b = (exitCode p = 0)} :=
    native "p.returncode == 0"
```

```aeon
def main (_:Int) : Unit :=
    p : CompletedProcess := Subprocess.run echoArgs;
    if Subprocess.succeeded p then
        print (Subprocess.stdout p)
    else
        print (Subprocess.stderr p)
```

If you want failure to be *impossible to ignore*, use `checkRun`, which raises
`CalledProcessError` on a non-zero exit. Because control only returns on
success, its result carries the postcondition `exitCode p = 0` — downstream code
can rely on success at the type level:

```aeon
def checkRun (argv: {a: (Array String) | Array.size a >= 1})
    : {p: CompletedProcess | exitCode p = 0} :=
    native "subprocess.run(argv, capture_output=True, text=True, check=True)"
```

### 3. Long-running children must be reaped — exactly once (QTT)

`run`/`checkRun` spawn, wait, and capture in one call. But when you start a child
now and reap it later (`subprocess.Popen`), a new bug class appears: forget to
`wait` and you leak a zombie / open pipes; `wait` twice and you misuse a spent
handle. That is a *linear-resource* discipline, so `Subprocess` also exposes a
multiplicity-1 `Process` handle — the same Quantitative Type Theory machinery as
[`Socket.ae`](https://github.com/alcides/aeon/blob/master/libraries/Socket.ae):

```aeon
type Process

def spawn  (argv: {a: (Array String) | Array.size a >= 1}) : Process
def wait   (1 p: Process) : Int     # blocks, reaps, returns exit code
def waitFor (seconds: {s:Float | s > 0.0}) (1 p: Process) : Int
def terminate (1 p: Process) : Int  # SIGTERM + wait
def kill      (1 p: Process) : Int  # SIGKILL + wait
```

Every consumer takes the handle at multiplicity 1, so a child bound with `let 1`
must be reaped exactly once via one of `wait` / `waitFor` / `terminate` / `kill`:

```aeon
def runDetached (argv: {a: (Array String) | Array.size a >= 1}) : Int :=
    let 1 p := Subprocess.spawn argv in
    Subprocess.wait p;
```

Drop the `wait` and the binder is left unconsumed:

```
>>> Linearity error: Linear binding p … is declared with multiplicity 1 but is never used.
```

— and waiting twice reports `… is used 2 times`. The leaked-process / zombie bug
becomes a compile error. For the full transactional version of this pattern
(commit-xor-rollback, close exactly once), see
[`Database`](database).

### Quick reference

| Function | Notes |
|---|---|
| `run argv` | argv-only, captures stdout/stderr |
| `runWithInput argv stdin` | feeds `stdin` to the child |
| `runWithTimeout argv seconds` | `seconds > 0`; raises `TimeoutExpired` |
| `checkRun argv` | result refined `exitCode p = 0` |
| `checkOutput argv` | success required; returns `stdout` only |
| `getExitCode p`, `succeeded p`, `stdout p`, `stderr p` | inspect a `CompletedProcess` |
| `spawn argv` → `Process` | **linear** handle; reap with one of below |
| `wait p`, `waitFor s p`, `terminate p`, `kill p` | consume the `Process` exactly once |

---

## A note on the trust boundary

As always with FFI, refinements over `native` are **promises the wrapper author
makes**, not facts the compiler verifies against the Python implementation (see
[the FFI guide](ffi#mental-model)). `getEnv`'s precondition is honest because
`os.environ[name]` really does raise iff `name` is unset; `checkRun`'s
postcondition is honest because `check=True` really does raise on a non-zero
exit. If you extend these modules, keep the refinement layer faithful to what
the Python call actually does.
