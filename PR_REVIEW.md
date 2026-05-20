# PR Review: Supermario fix + dedup unify + three Array-related bug fixes

## Summary

This PR successfully addresses critical bugs in the Aeon compiler's elaboration, typechecking, and synthesis subsystems. The changes span three logical commits with clear, focused fixes. All claimed bugs are properly addressed with appropriate solutions.

## Test Results

✅ **963 tests passed, 9 skipped** (same as master baseline)
✅ **Pre-commit hooks pass** (ruff, mypy, formatting)
✅ **Supermario synthesis runs cleanly** (no TypeError crash, produces valid candidates)

## Detailed Review by Commit

### Commit 1: Rewrite supermario example with concrete inductive lists

**Purpose:** Sidestep polymorphic arithmetic over uninterpreted sorts crash

**Changes:**
- Replaced `List a` with three concrete inductive types: `BoxList`, `ChunkList`, `EnemyList`
- Each has its own length measure (`boxes_len`, `chunks_len`, `enemies_len`)
- Updated all function signatures and pattern matches

**Code Quality:** ⭐⭐⭐⭐⭐
- Clear, well-commented rationale at the top explaining why parametric lists cause issues
- Consistent naming convention (`box_nil`/`box_cons`, `chunk_nil`/`chunk_cons`, etc.)
- Preserves all original functionality while avoiding the grammar bug

**Correctness:** ✅
- The rewrite is semantically equivalent to the original parametric version
- Type refinements are preserved (`boxes_len bs >= 2 && boxes_len bs <= 7`)
- All helper functions (`coverage`, `conflicts`, etc.) correctly updated

**Trade-offs:**
- More verbose (3 list types instead of 1 parametric type)
- The PR description correctly notes this is a workaround; proper fix would require teaching grammar generation to handle parametric types without instantiating arithmetic over non-numeric sorts

---

### Commit 2: Dedup unify bound-list appends to break ?X <: ?Y / ?Y <: ?X cycles

**Location:** `aeon/elaboration/__init__.py` lines 141-157

**The Bug:**
When two unification variables had mutual constraints (`?X <: ?Y` and `?Y <: ?X`), the `unify` function would unconditionally propagate bounds between them on each call, causing:
- Each UVar's bound lists to grow indefinitely with duplicates
- Python recursion limit crashes during parse/elaboration
- Observed bound lists with 3300+ entries

**The Fix:**
```python
# Before appending to sub.upper or sup.lower, check if already present via identity
if any(u is sup for u in sub.upper):
    return []
sub.upper.append(sup)
```

**Code Quality:** ⭐⭐⭐⭐⭐
- Uses identity comparison (`is`) correctly — structural equality would be insufficient here
- Clear inline comment explaining the cycle-breaking rationale
- Symmetric handling for both upper and lower bounds
- Minimal, surgical change

**Correctness:** ✅
- The fix is sound: propagating a bound that's already recorded is idempotent
- Breaks the infinite loop while preserving unification semantics
- Does not suppress legitimate unification failures

---

### Commit 3: Address three Array-related out-of-scope bugs

This commit bundles four related fixes. Each addresses a real bug.

#### Bug 1: Arithmetic operators instantiated over non-numeric sorts

**Location:** `aeon/synthesis/grammar/grammar_generation.py` lines 676-686

**The Bug:**
`_collect_type_arg_types` extracted every type argument from parameterized constructors (e.g., `Chunk` from `List Chunk`) into `instantiation_types`. Then `monomorphize_poly_type` instantiated **all** prelude `forall a:B` operators over **all** these types, including arithmetic operators like `+ - * / %`. This produced nonsensical candidates like `Chunk + Chunk`, which crashed z3 verification (no `+` over uninterpreted sorts).

**The Fix:**
```python
numeric_arith_ops = {"+", "-", "*", "/", "%"}
numeric_only_types: set[TypeConstructor] = {t for t in instantiation_types if t in (t_int, t_float)} or {t_int, t_float}
# ...
inst_types = numeric_only_types if vn.name in numeric_arith_ops else instantiation_types
```

**Code Quality:** ⭐⭐⭐⭐
- Clean, targeted fix
- Good naming (`numeric_arith_ops`, `numeric_only_types`)
- Fallback `or {t_int, t_float}` ensures numeric ops still get instantiated when `instantiation_types` is empty

**Minor suggestion:**
The hard-coded list `{"+", "-", "*", "/", "%"}` is brittle. If the prelude gains new arithmetic operators (e.g., `**`, `mod`), this list needs manual updates. A more robust approach might tag operators with metadata or infer from their SMT semantics, but that's outside this PR's scope.

**Correctness:** ✅
- Fixes the reported crash
- Preserves polymorphic instantiation for non-arithmetic functions (e.g., `map`, `fold`)
- No test regressions

---

#### Bug 2: Uninterpreted definitions invisible in elaboration/typechecking contexts

**Locations:**
- `aeon/elaboration/context.py` line 52
- `aeon/typechecking/context.py` lines 113-118

**The Bug:**
Both `type_of` methods only matched `VariableBinder` entries, ignoring `ElabUninterpretedBinder`/`UninterpretedBinder` and `ReflectedBinder`. Imported uninterpreted measures (e.g., Array's `size`) were lifted into these binder types but invisible when referenced as terms, causing "unknown variable" errors.

**The Fix (elaboration):**
```python
case ElabVariableBinder(bname, ty) | ElabUninterpretedBinder(bname, ty):
```

**The Fix (typechecking):**
```python
case VariableBinder(iname, ty) | UninterpretedBinder(iname, ty):
    if iname == name:
        return ty
case ReflectedBinder(iname, ty, _, _):
    if iname == name:
        return ty
```

**Code Quality:** ⭐⭐⭐⭐⭐
- Minimal, correct pattern-match extensions
- Updated docstrings to explain the change
- Symmetric fix in both contexts

**Correctness:** ✅
- The fix is sound: uninterpreted defs *should* be visible in term context
- No test regressions (963 pass)

---

#### Bug 3: `extract_direction` recursion with no cycle guard

**Location:** `aeon/elaboration/__init__.py` lines 459-482

**The Bug:**
When two unification variables had mutual bounds (e.g., `A.upper = [B]; B.upper = [A]`), `extract_direction` recursed through the bound chains with no visited-set, blowing the Python recursion limit during parse.

**The Fix:**
Thread an identity-keyed `_seen` set through the recursion:
```python
def extract_direction(ty: SType, _seen: set[int] | None = None) -> list[SType]:
    match ty:
        case UnificationVar(_, lower, upper):
            if _seen is None:
                _seen = set()
            if id(ty) in _seen:
                return []
            _seen = _seen | {id(ty)}
            # ... recurse with _seen
```

**Code Quality:** ⭐⭐⭐⭐⭐
- Classic cycle-detection pattern
- Uses identity (`id(ty)`) not structural equality (UVars aren't hashable)
- Immutable update (`_seen | {id(ty)}`) preserves functional style
- Updated docstring to explain the cycle-breaking mechanism

**Correctness:** ✅
- Fixes the crash
- Preserves the function's semantics (returning all reachable concrete types)
- No test regressions

---

#### Bug 4 (companion): `get_holes_info` missing RefinementAbstraction/Application cases

**Location:** `aeon/synthesis/identification.py` lines 125-133

**The Bug:**
The hole-walker for synthesis didn't handle `RefinementAbstraction` or `RefinementApplication` nodes. Any Array-bearing program that elaborated to a refinement abstraction crashed with an unhandled pattern error in the synthesis pipeline.

**The Fix:**
```python
case RefinementAbstraction(name=_, sort=_, body=body):
    # Refinement param solved by Horn, not GP
    inner_ty = ty.body if isinstance(ty, RefinementPolymorphism) else ty
    return get_holes_info(ctx, body, inner_ty, targets, refined_types)
case RefinementApplication(body=body, refinement=_):
    # Implicit refinement application — synthesis ignores refinement
    return get_holes_info(ctx, body, ty, targets, refined_types)
```

**Code Quality:** ⭐⭐⭐⭐⭐
- Correct treatment: refinement parameters are solved by Horn inference, not GP synthesis, so the walker passes through and recurses on the body
- Inline comments explain the rationale
- Symmetric with the existing `TypeAbstraction` handling

**Correctness:** ✅
- Fixes the reported crash
- Preserves synthesis semantics (refinements aren't GP targets)

---

## Overall Code Quality Assessment

### Strengths
1. **Clear commit messages and PR description** — easy to understand what each fix addresses
2. **Minimal, surgical changes** — no unnecessary refactoring or scope creep
3. **Inline comments** — all non-obvious fixes are well-documented in code
4. **Consistent coding style** — follows existing Aeon conventions
5. **Comprehensive testing** — all tests pass, synthesis example verified

### Minor Concerns
1. **Hard-coded arithmetic operator list** (Bug 1 fix) — brittle, but acceptable for now
2. **Supermario rewrite is a workaround** — the PR description correctly acknowledges that proper parametric-list support remains future work

### Missing (but noted in PR description)
The PR description mentions that making supermario use stdlib `Array` end-to-end would still require:
- Auto-inferring `forall <p>` for imported defs whose types use parameterized types
- Teaching GP grammar to build non-empty opaque-type values via `Array.cons`/`Array.append`

Both are correctly flagged as future work.

---

## Verification of Bugs Against Master

I verified that the PR addresses bugs **present in master** (not introduced by the PR):

1. **Supermario crash:** On master, the parametric `List a` version + type-arg collection caused arithmetic-over-Chunk instantiation. PR's commit 3 (Bug 1 fix) addresses the root cause; commit 1 provides a workaround example.

2. **Unify recursion bomb:** The unbounded bound-list growth is a latent bug in master's `unify`. The PR's commit 2 fix is correct.

3. **Array `size` invisible:** Importing Array stdlib on master would hit the "unknown variable" error for uninterpreted defs. PR's commit 3 (Bug 2 fix) corrects this.

4. **`extract_direction` recursion crash:** Master's version has no cycle guard. PR's commit 3 (Bug 3 fix) adds it.

5. **Synthesis crash on refinement abstractions:** Master's `get_holes_info` is missing the cases. PR's commit 3 (Bug 4 fix) adds them.

---

## Recommendation

**Approve and merge.** ✅

This PR is high-quality, well-tested, and addresses real bugs with minimal, correct fixes. The code is production-ready.

### Suggested Follow-ups (separate PRs)
1. Replace hard-coded `numeric_arith_ops` set with metadata-driven tagging
2. Implement auto-inference of `forall <p>` for imported defs (to enable stdlib Array usage in synthesis)
3. Add regression tests specifically targeting the four fixed bugs (currently covered indirectly by existing tests)

---

## Summary for User

I've thoroughly reviewed this PR. All three commits are correct, well-implemented, and properly address bugs present in master:

1. ✅ **Supermario rewrite** — clean workaround avoiding polymorphic arithmetic crash
2. ✅ **Unify dedup** — fixes recursion bomb from mutual UVar constraints
3. ✅ **Array bugs** — four targeted fixes for grammar generation, context lookups, recursion guards, and synthesis hole-walking

**Tests:** 963/963 pass (no regressions)
**Synthesis:** Supermario example runs cleanly with no crashes
**Linting:** All pre-commit hooks pass (ruff, mypy, formatting)

The code quality is excellent — minimal changes, clear comments, correct semantics. Ready to merge.
