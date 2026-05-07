# Existentials replacing ANF — Phase 0 spike

Status: **AST scaffolding only.** This document describes the target design;
the actual rewrite of `synth`, `sub`, SMT, and the deletion of ANF will land
in subsequent commits on this branch.

## Why

ANF (`aeon/frontend/anf_converter.py`) hoists every non-trivial argument into
a `let` so that refinement substitution always has a name to latch onto:

```text
f (g a)        ⇒  let _anf = g a in f _anf
```

Those synthesised `let` bindings are invisible aliases for their right-hand
side. They are harmless today, but they get in the way the moment we add:

1. **Move semantics on `let` for linear values** (Phase 3 of the QTT plan):
   `let _anf = consume_once_value in f _anf` either double-consumes or
   silently drops the consumption.
2. **Latte alias tracking**: ANF synthesises pairs `(_anf, g a)` that look
   like fresh bindings but are really equalities Latte already knows about,
   muddying the alias graph.

Carrying the synthesised binder in the *type* instead of the term keeps the
syntactic `let` count equal to what the user wrote.

## Form B (chosen)

A type optionally has a list of existential binders at its outermost layer:

```python
@dataclass
class ExistentialType(Type):
    binders: tuple[tuple[Name, Type], ...]
    body: Type
```

- **Binders are flat.** Constructors flatten nested `ExistentialType`s via
  `with_binders`; the body is never itself an `ExistentialType`.
- **Refinements live in binders.** `binders[i]` is typically
  `(name, RefinedType(name, base, predicate))`, where the refinement carries
  *both* the static info (`base > 0`) and the equation (`name == g a`) when
  the binder was created from a syntactic call.
- **Bodies are bare.** A body is one of `TypeConstructor`, `TypeVar`, or
  `AbstractionType`. Never `RefinedType`, never `ExistentialType`.

Example. With

```aeon
def inc (n: Int) : { m: Int | m == n + 1 } = n + 1;
def safe_div (a: Int) (b: { n: Int | n != 0 }) : Int = a / b;
```

the type of `inc 0` is

```text
[ _y : { ℓ : Int | ℓ == 1 } ]   Int
```

and the type of `inc (inc 0)` is

```text
[ _y₁ : { ℓ : Int | ℓ == 1 },
  _y₂ : { ℓ : Int | ℓ == _y₁ + 1 } ]   Int
```

Subtyping `[ binders ] body  <:  T` opens the existential by skolemising each
binder name (introducing it into the verification context with its refinement
as an assumption) and then discharging `body <: T` with the binder names
known. Argument-position binders flow *out* through application: when synth
sees `f x` and `x` synthesises to `[bs] body_x`, the binders `bs` are pulled
to the outside of the result type rather than being trapped inside.

## Surface-language impact

None at this phase. The grammar does not gain any existential syntax; the
binders are an internal construct introduced by `synth`. Users keep writing
the same programs.

## Phase 0 work plan

1. **AST node** (this commit). `ExistentialType` + `with_binders` smart
   constructor in `aeon/core/types.py`. Substitution / bind / lift / lower
   are *not yet* updated; those calls will assert if they encounter an
   existential, which is fine because nothing produces one yet.

2. **`synth(Application)`** in `aeon/typechecking/typeinfer.py`:
   - Synth the argument, getting `(c_arg, ty_arg)`.
   - If `ty_arg` is `ExistentialType(bs, body)`, lift `bs` outward.
   - If the function's parameter type is `(x: T) -> U`, allocate a fresh
     `_y`, refine `T` to `{ _y : base(T) | predicate(T) ∧ _y == arg }`
     when `arg` is a name or literal, otherwise `{ _y : base(T) | predicate(T) }`,
     and prepend `(_y, refined)` to the result type's binders.
   - Substitute `Var(_y)` for `x` in the body.

3. **`sub`** in `aeon/verification/sub.py`: when the subtype is
   `ExistentialType(bs, body)`, fold each binder into the verification
   context as a fresh skolem with its refinement as a precondition, then
   recurse with `body` against the supertype.

4. **SMT translation** in `aeon/verification/smt.py`: existential binders
   become fresh constants (Skolem witnesses) under the assumption of their
   refinement. Z3 already handles existential quantification natively but
   we won't need it: the binders only appear in *subtype* positions (left
   of `<:`), where skolemisation is sound.

5. **Remove ANF from the typechecker pipeline.** `tests/driver.py`, the
   four end-to-end / decreasing-by / intlist regression tests, and
   `aeon/synthesis/entrypoint.py` no longer call `ensure_anf`. The
   `test_precedence` test that asserted ANF idempotence is gone with
   ANF as a public concept.

6. **Production driver and LLVM backend still run ANF as a defensive
   pass.** The typechecker passes the full test suite (425/425) without
   ANF, but two downstream consumers remain coupled to flat let-chains:

   - The LLVM IR builder in `aeon/llvm/cpu/converter.py` walks
     `Application` nodes assuming the spine has been linearised by ANF.
   - The SMT translation in `aeon/verification/smt.py` raises a
     `Z3Exception` on a handful of production-pipeline programs (e.g.
     `examples/PSB2/solved/bowling.ae`) when their refinements are built
     from existential-bound names; this needs a deeper trace to pin
     down whether it's a missed binder skolemisation or a capture issue.

   Until those land, `aeon/facade/driver.py` keeps a one-line call to
   `ensure_anf` after `bind_ids`; the call is documented in-source. The
   converter file (`aeon/frontend/anf_converter.py`) therefore stays in
   the tree for now.

## Open questions still on the table

- **SMT for existentials**: the bowling example trips
  `translate_liq` returning a non-Z3 value through `LiquidVar` lookup.
  The fix likely involves teaching the SMT context to walk binders the
  same way `sub`'s `implication_constraint` chain does.
- **Binder ordering matters for refinements that mention earlier binders.**
  Verify this is preserved through `sub` and the SMT translation.
- **Polymorphism interaction.** Type variables can appear inside refined
  binder types; the existing `TypePolymorphism` handling needs a recursion
  case.
- **Hashing / equality of existentials.** Currently structural; if we want
  alpha-equivalence, add a normalisation pass that renames binders to a
  canonical scheme before comparison.
- **LLVM converter**: rewrite `visit_call` to fold inline applications,
  so the LLVM path can drop its defensive ANF pass.
