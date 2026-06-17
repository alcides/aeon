from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidLiteralUnit,
    LiquidTerm,
    LiquidVar,
)
from aeon.utils.name import Name
from aeon.core.terms import (
    Term,
    Literal,
    Var,
    Application,
    Abstraction,
    Let,
    Rec,
    If,
    RefinementAbstraction,
    RefinementApplication,
    TypeAbstraction,
    TypeApplication,
)
from aeon.core.types import (
    LiquidHornApplication,
    Type,
    TypeVar,
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    TypePolymorphism,
    TypeConstructor,
    Top,
)


def _rename_liquid_parallel(lq: LiquidTerm, mapping: dict[Name, Name]) -> LiquidTerm:
    """Simultaneously rename every variable occurrence in a liquid term.

    Each ``LiquidVar``/application head is rewritten according to ``mapping`` in a
    single pass, so a name introduced by one entry is never re-substituted by
    another (unlike chained single-variable substitutions). This is what makes
    ``canonicalize_type`` safe to apply to an already-canonical type.
    """
    match lq:
        case LiquidVar(name):
            return LiquidVar(mapping.get(name, name))
        case LiquidApp(fun, args):
            return LiquidApp(mapping.get(fun, fun), [_rename_liquid_parallel(a, mapping) for a in args])
        case LiquidHornApplication(fun, argtypes, loc):
            return LiquidHornApplication(
                mapping.get(fun, fun),
                [(_rename_liquid_parallel(a, mapping), t) for (a, t) in argtypes],
                loc=loc,
            )
        case _:
            return lq


def core_liquid_equality(lq1: LiquidTerm, lq2: LiquidTerm, rename_left: dict[Name, Name] | None = None) -> bool:
    "Equality of liquid terms up to alpha renaming"
    rename_left = rename_left or {}
    match lq1, lq2:
        case LiquidVar(an), LiquidVar(bn):
            return rename_left.get(an, an) == bn
        case LiquidLiteralBool(a), LiquidLiteralBool(b):
            return a == b
        case LiquidLiteralInt(a), LiquidLiteralInt(b):
            return a == b
        case LiquidLiteralFloat(a), LiquidLiteralFloat(b):
            return a == b
        case LiquidLiteralString(a), LiquidLiteralString(b):
            return a == b
        case LiquidLiteralUnit(), LiquidLiteralUnit():
            return True
        case LiquidApp(a1, a2), LiquidApp(b1, b2):
            return a1 == b1 and all(core_liquid_equality(i2, j2, rename_left) for (i2, j2) in zip(a2, b2))
        case LiquidHornApplication(a1, _), LiquidHornApplication(b1, _):
            return a1 == b1
        case _:
            return False


def core_type_equality(type1: Type, type2: Type, rename_left: dict[Name, Name] | None = None) -> bool:
    "Equality of types up to alpha renaming"
    rename_left = rename_left or {}
    match type1, type2:
        case TypeVar(an), TypeVar(bn):
            return rename_left.get(an, an) == bn
        case RefinedType(aname, aty, aref), RefinedType(bname, bty, bref):
            return core_type_equality(aty, bty, rename_left) and core_liquid_equality(
                aref, bref, rename_left | {aname: bname}
            )
        case AbstractionType(aname, a1, a2), AbstractionType(bname, b1, b2):
            return core_type_equality(a1, b1, rename_left) and core_type_equality(a2, b2, rename_left | {aname: bname})
        case TypeConstructor(aname, a1), TypeConstructor(bname, b1):
            return aname == bname and all(core_type_equality(a, b, rename_left) for a, b in zip(a1, b1))
        case TypePolymorphism(aname, akind, abody), TypePolymorphism(bname, bkind, bbody):
            return akind == bkind and core_type_equality(abody, bbody, rename_left | {aname: bname})
        case RefinementPolymorphism(aname, asort, abody), RefinementPolymorphism(bname, bsort, bbody):
            return core_type_equality(asort, bsort, rename_left) and core_type_equality(
                abody, bbody, rename_left | {aname: bname}
            )
        case Top(), Top():
            return True
        case _:
            return False


def canonicalize_type(
    ty: Type,
    rename: dict[Name, Name] | None = None,
    counter: list[int] | None = None,
) -> Type:
    """Rebuilds a type into a deterministic alpha-equivalence normal form.

    Every binder (and its bound occurrences) is renamed to a positional name
    (``Name("__c0__", 0)``, ``Name("__c1__", 0)``, ...) allocated from a single
    shared pre-order counter threaded through the recursion. As a result, two
    types are alpha-equivalent iff their canonical forms are structurally equal
    (and so compare equal / hash equal via the structural ``__eq__``/``__hash__``
    in ``aeon/core/types.py``).
    """
    rename = rename or {}
    if counter is None:
        counter = [0]

    def fresh() -> Name:
        n = Name(f"__c{counter[0]}__", 0)
        counter[0] += 1
        return n

    match ty:
        case TypeVar(name):
            return TypeVar(rename.get(name, name))
        case TypeConstructor(name, args):
            return TypeConstructor(name, [canonicalize_type(a, rename, counter) for a in args])
        case AbstractionType(var_name, var_type, return_type):
            c_var_type = canonicalize_type(var_type, rename, counter)
            fresh_name = fresh()
            c_return_type = canonicalize_type(return_type, rename | {var_name: fresh_name}, counter)
            return AbstractionType(fresh_name, c_var_type, c_return_type, multiplicity=ty.multiplicity)
        case RefinedType(name, inner, refinement):
            c_inner = canonicalize_type(inner, rename, counter)
            fresh_name = fresh()
            # Rebind the refinement's own bound variable to the fresh canonical name
            # and rewrite free variables captured by enclosing binders in a single
            # parallel pass. The bound variable shadows any enclosing binder of the
            # same name, so its mapping takes precedence. Doing this as two sequential
            # substitutions is unsafe when the type is re-canonicalized: a freshly
            # allocated ``__cN__`` name can collide with a stale ``__cN__`` key still
            # present in ``rename``, chaining the bound variable through an unrelated
            # rewrite and producing a refinement whose binder and body disagree.
            body_map = {old: new for (old, new) in rename.items() if old != name}
            body_map[name] = fresh_name
            c_ref = _rename_liquid_parallel(refinement, body_map)
            assert isinstance(c_inner, (TypeConstructor, TypeVar))
            return RefinedType(fresh_name, c_inner, c_ref)
        case TypePolymorphism(name, kind, body):
            fresh_name = fresh()
            c_body = canonicalize_type(body, rename | {name: fresh_name}, counter)
            return TypePolymorphism(fresh_name, kind, c_body)
        case RefinementPolymorphism(name, sort, body):
            c_sort = canonicalize_type(sort, rename, counter)
            fresh_name = fresh()
            c_body = canonicalize_type(body, rename | {name: fresh_name}, counter)
            return RefinementPolymorphism(fresh_name, c_sort, c_body)
        case Top():
            return ty
        case _:
            assert False, f"Unsupported type in canonicalize_type: {ty} ({type(ty)})"


def core_term_equality(term1: Term, term2: Term, rename_left: dict[Name, Name] | None = None) -> bool:
    "Equality of terms up to alpha renaming"
    rename_left = rename_left or {}
    match term1, term2:
        case Var(an), Var(bn):
            return rename_left.get(an, an) == bn
        case Literal(av, at), Literal(bv, bt):
            return av == bv and core_type_equality(at, bt, rename_left)
        case Application(a1, a2), Application(b1, b2):
            return core_term_equality(a1, b1, rename_left) and core_term_equality(a2, b2, rename_left)
        case Abstraction(an, abody), Abstraction(bn, bbody):
            return core_term_equality(abody, bbody, rename_left | {an: bn})
        case Let(aname, aval, acont), Let(bname, bval, bcont):
            return core_term_equality(aval, bval, rename_left) and core_term_equality(
                acont, bcont, rename_left | {aname: bname}
            )
        case Rec(aname, atype, aval, acont, adecr), Rec(bname, btype, bval, bcont, bdecr):
            nrename = rename_left | {aname: bname}
            return (
                core_term_equality(aval, bval, nrename)
                and core_type_equality(atype, btype, rename_left)
                and core_term_equality(acont, bcont, nrename)
                and len(adecr) == len(bdecr)
                and all(core_term_equality(x, y, nrename) for x, y in zip(adecr, bdecr, strict=True))
            )
        case If(ac, at, ao), If(bc, bt, bo):
            return (
                core_term_equality(ac, bc, rename_left)
                and core_term_equality(at, bt, rename_left)
                and core_term_equality(ao, bo, rename_left)
            )
        case TypeApplication(ab, at), TypeApplication(bb, bt):
            return core_term_equality(ab, bb, rename_left) and core_type_equality(at, bt, rename_left)
        case TypeAbstraction(aname, akind, abody), TypeAbstraction(bname, bkind, bbody):
            return akind == bkind and core_term_equality(abody, bbody, rename_left | {aname: bname})
        case RefinementAbstraction(aname, asort, abody), RefinementAbstraction(bname, bsort, bbody):
            return core_type_equality(asort, bsort, rename_left) and core_term_equality(
                abody, bbody, rename_left | {aname: bname}
            )
        case RefinementApplication(ab, ar), RefinementApplication(bb, br):
            return core_term_equality(ab, bb, rename_left) and core_term_equality(ar, br, rename_left)
        case _:
            return False
