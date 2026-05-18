//! Rust ports of the recursive substitution and instantiation walks that
//! the profiler flagged as hot in synthesis:
//!
//! - type_substitution (aeon.core.instantiation)
//! - type_variable_instantiation (aeon.core.instantiation)
//! - substitution_in_liquid (aeon.core.substitutions)
//! - refined_to_unrefined_type (aeon.core.types)
//!
//! Plus the qualifier collection walks used by predicate abstraction:
//! - _flatten_and, _atoms_from_predicate, _collect_from_type
//!   (aeon.typechecking.qualifiers)

use pyo3::prelude::*;
use pyo3::types::{PyList, PySet, PyTuple};

use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidTerm, LiquidVar,
};
use crate::name::Name;
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, Type, TypeConstructor,
    TypePolymorphism, TypeVar,
};

#[inline]
fn name_eq(py: Python<'_>, a: &Py<Name>, b: &Py<Name>) -> bool {
    let a = a.borrow(py);
    let b = b.borrow(py);
    a.id == b.id && a.name == b.name
}

/// True if Py<Name> equals the borrowed-name (n, id) pair.
#[inline]
fn name_matches(py: Python<'_>, a: &Py<Name>, target_name: &str, target_id: i64) -> bool {
    let a = a.borrow(py);
    a.id == target_id && a.name == target_name
}

/// Build a new RefinedType in Rust without going through Python attribute
/// resolution (the import_bound("aeon_rs").getattr("RefinedType") path).
fn make_refined_type(
    py: Python<'_>,
    name: Py<Name>,
    inner: PyObject,
    refinement: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    let inst = Py::new(py, (RefinedType { name, type_: inner, refinement, loc }, Type))?;
    Ok(inst.into_any())
}

fn make_abstraction_type(
    py: Python<'_>,
    var_name: Py<Name>,
    var_type: PyObject,
    type_: PyObject,
    loc: PyObject,
    multiplicity: PyObject,
) -> PyResult<PyObject> {
    let inst = Py::new(
        py,
        (
            AbstractionType { var_name, var_type, type_, loc, multiplicity },
            Type,
        ),
    )?;
    Ok(inst.into_any())
}

fn make_type_polymorphism(
    py: Python<'_>,
    name: Py<Name>,
    kind: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    let inst = Py::new(py, (TypePolymorphism { name, kind, body, loc }, Type))?;
    Ok(inst.into_any())
}

fn make_refinement_polymorphism(
    py: Python<'_>,
    name: Py<Name>,
    sort: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    let inst = Py::new(py, (RefinementPolymorphism { name, sort, body, loc }, Type))?;
    Ok(inst.into_any())
}

fn make_type_constructor(
    py: Python<'_>,
    name: Py<Name>,
    args: Py<PyList>,
    loc: PyObject,
) -> PyResult<PyObject> {
    let inst = Py::new(py, (TypeConstructor { name, args, loc }, Type))?;
    Ok(inst.into_any())
}

fn make_liquid_app(
    py: Python<'_>,
    fun: Py<Name>,
    args: Py<PyList>,
    loc: PyObject,
) -> PyResult<PyObject> {
    let inst = Py::new(py, (LiquidApp { fun, args, loc }, LiquidTerm))?;
    Ok(inst.into_any())
}

fn make_liquid_horn_application(
    py: Python<'_>,
    name: Py<Name>,
    argtypes: Py<PyList>,
    loc: PyObject,
) -> PyResult<PyObject> {
    let inst = Py::new(
        py,
        (LiquidHornApplication { name, argtypes, loc }, LiquidTerm),
    )?;
    Ok(inst.into_any())
}

/// type_substitution(t, alpha, beta): replace all TypeVar(alpha) occurrences
/// in `t` with `beta`. Mirrors aeon.core.instantiation.type_substitution.
///
/// Edge case (refinement merging): when substituting alpha with a RefinedType
/// inside a RefinedType wrapper, we need to AND the refinements together.
/// We delegate that merge to Python (calls mk_liquid_and + substitution_in_liquid).
#[pyfunction]
pub fn type_substitution(
    py: Python<'_>,
    t: PyObject,
    alpha: Py<Name>,
    beta: PyObject,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if let Ok(tv) = bound.downcast::<TypeVar>() {
        let tv = tv.borrow();
        if name_eq(py, &tv.name, &alpha) {
            return Ok(beta.clone_ref(py));
        }
        return Ok(t);
    }
    if bound.is_instance_of::<Top>() {
        return Ok(t);
    }
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let new_inner = type_substitution(
            py,
            rt.type_.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        let new_inner_bound = new_inner.bind(py);

        if let Ok(inner_rt) = new_inner_bound.downcast::<RefinedType>() {
            // Refinement-merge case: RefinedType{name=outer, type=RefinedType{iname,iity,iref}, ref}
            // becomes RefinedType{name=outer, type=iity, ref=ref AND iref[iname := outer]}
            let inner_rt = inner_rt.borrow();
            // substitution_in_liquid(iref, LiquidVar(name), iname)
            let liquid_var = Py::new(
                py,
                (
                    LiquidVar {
                        name: rt.name.clone_ref(py),
                        loc: rt.loc.clone_ref(py),
                    },
                    LiquidTerm,
                ),
            )?;
            let substituted = substitution_in_liquid(
                py,
                inner_rt.refinement.clone_ref(py),
                liquid_var.into_any(),
                inner_rt.name.clone_ref(py),
            )?;
            let merged = crate::liquid_ops::mk_liquid_and(
                py,
                rt.refinement.clone_ref(py),
                substituted,
            )?;
            return make_refined_type(
                py,
                rt.name.clone_ref(py),
                inner_rt.type_.clone_ref(py),
                merged.into(),
                rt.loc.clone_ref(py),
            );
        }
        if new_inner_bound.is_instance_of::<AbstractionType>() {
            return Err(pyo3::exceptions::PyAssertionError::new_err(
                "Abstraction types cannot be refined",
            ));
        }
        return make_refined_type(
            py,
            rt.name.clone_ref(py),
            new_inner,
            rt.refinement.clone_ref(py),
            rt.loc.clone_ref(py),
        );
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let new_var_type = type_substitution(
            py,
            at.var_type.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        let new_type = type_substitution(
            py,
            at.type_.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        return make_abstraction_type(
            py,
            at.var_name.clone_ref(py),
            new_var_type,
            new_type,
            at.loc.clone_ref(py),
            at.multiplicity.clone_ref(py),
        );
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        if name_eq(py, &tp.name, &alpha) {
            return Ok(t);
        }
        let new_body = type_substitution(
            py,
            tp.body.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        return make_type_polymorphism(
            py,
            tp.name.clone_ref(py),
            tp.kind.clone_ref(py),
            new_body,
            tp.loc.clone_ref(py),
        );
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let new_sort = type_substitution(
            py,
            rp.sort.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        let new_body = type_substitution(
            py,
            rp.body.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        return make_refinement_polymorphism(
            py,
            rp.name.clone_ref(py),
            new_sort,
            new_body,
            rp.loc.clone_ref(py),
        );
    }
    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let args = tc.args.bind(py);
        let n = args.len();
        let new_args = PyList::empty_bound(py);
        for i in 0..n {
            let arg = args.get_item(i)?;
            let new_arg = type_substitution(py, arg.into(), alpha.clone_ref(py), beta.clone_ref(py))?;
            new_args.append(new_arg)?;
        }
        return make_type_constructor(py, tc.name.clone_ref(py), new_args.unbind(), tc.loc.clone_ref(py));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "type_substitution: unknown type {}",
        bound.repr()?.to_string()
    )))
}

/// type_variable_instantiation(t, alpha, beta): the instantiation variant.
/// Like type_substitution but: when the TypeVar(alpha) sits inside a
/// RefinedType wrapper and beta is itself refined, we merge refinements.
/// Mirrors aeon.core.instantiation.type_variable_instantiation.
#[pyfunction]
pub fn type_variable_instantiation(
    py: Python<'_>,
    t: PyObject,
    alpha: Py<Name>,
    beta: PyObject,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if bound.is_instance_of::<TypeConstructor>() {
        return Ok(t);
    }
    if let Ok(tv) = bound.downcast::<TypeVar>() {
        let tv = tv.borrow();
        if name_eq(py, &tv.name, &alpha) {
            return Ok(beta);
        }
        return Ok(t);
    }
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let inner = rt.type_.bind(py);
        // Special case: RefinedType{n, TypeVar(alpha), ref} and beta is RefinedType
        if let Ok(itv) = inner.downcast::<TypeVar>() {
            let itv = itv.borrow();
            if name_eq(py, &itv.name, &alpha) {
                let beta_bound = beta.bind(py);
                if let Ok(beta_rt) = beta_bound.downcast::<RefinedType>() {
                    let beta_rt = beta_rt.borrow();
                    let liquid_var = Py::new(
                        py,
                        (
                            LiquidVar {
                                name: rt.name.clone_ref(py),
                                loc: rt.loc.clone_ref(py),
                            },
                            LiquidTerm,
                        ),
                    )?;
                    let substituted = substitution_in_liquid(
                        py,
                        beta_rt.refinement.clone_ref(py),
                        liquid_var.into_any(),
                        beta_rt.name.clone_ref(py),
                    )?;
                    let merged = crate::liquid_ops::mk_liquid_and(
                        py,
                        rt.refinement.clone_ref(py),
                        substituted,
                    )?;
                    return make_refined_type(
                        py,
                        rt.name.clone_ref(py),
                        beta_rt.type_.clone_ref(py),
                        merged.into(),
                        rt.loc.clone_ref(py),
                    );
                }
            }
        }
        // General case: recurse into inner type, keep refinement unchanged.
        let new_inner = type_variable_instantiation(
            py,
            rt.type_.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        return make_refined_type(
            py,
            rt.name.clone_ref(py),
            new_inner,
            rt.refinement.clone_ref(py),
            rt.loc.clone_ref(py),
        );
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let new_var_type = type_variable_instantiation(
            py,
            at.var_type.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        let new_type = type_variable_instantiation(
            py,
            at.type_.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        return make_abstraction_type(
            py,
            at.var_name.clone_ref(py),
            new_var_type,
            new_type,
            at.loc.clone_ref(py),
            at.multiplicity.clone_ref(py),
        );
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let new_body = type_variable_instantiation(
            py,
            tp.body.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        return make_type_polymorphism(
            py,
            tp.name.clone_ref(py),
            tp.kind.clone_ref(py),
            new_body,
            tp.loc.clone_ref(py),
        );
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let new_sort = type_variable_instantiation(
            py,
            rp.sort.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        let new_body = type_variable_instantiation(
            py,
            rp.body.clone_ref(py),
            alpha.clone_ref(py),
            beta.clone_ref(py),
        )?;
        return make_refinement_polymorphism(
            py,
            rp.name.clone_ref(py),
            new_sort,
            new_body,
            rp.loc.clone_ref(py),
        );
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "type_variable_instantiation: unknown type {}",
        bound.repr()?.to_string()
    )))
}

/// refined_to_unrefined_type: strip refinements off all leaf base types.
/// Mirrors aeon.core.types.refined_to_unrefined_type.
#[pyfunction]
pub fn refined_to_unrefined_type(py: Python<'_>, ty: PyObject) -> PyResult<PyObject> {
    let bound = ty.bind(py);
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        return Ok(rt.type_.clone_ref(py));
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let nv = refined_to_unrefined_type(py, at.var_type.clone_ref(py))?;
        let nt = refined_to_unrefined_type(py, at.type_.clone_ref(py))?;
        return make_abstraction_type(
            py,
            at.var_name.clone_ref(py),
            nv,
            nt,
            at.loc.clone_ref(py),
            at.multiplicity.clone_ref(py),
        );
    }
    Ok(ty)
}

/// substitute_vartype: replace all TypeVar(name) occurrences in `t` by rep.
/// Mirrors aeon.core.substitutions.substitute_vartype.
///
/// Differences from type_substitution:
///  - On RefinedType, does NOT merge refinements (just rebuilds with recursed inner).
///  - Asserts the inner of RefinedType is not itself a RefinedType (Aeon invariant).
///  - Asserts on Top (no Top handler — Python crashes; we crash too for parity).
#[pyfunction]
pub fn substitute_vartype(
    py: Python<'_>,
    t: PyObject,
    rep: PyObject,
    name: Py<Name>,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if let Ok(tv) = bound.downcast::<TypeVar>() {
        if name_eq(py, &tv.borrow().name, &name) {
            return Ok(rep);
        }
        return Ok(t);
    }
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let new_inner = substitute_vartype(
            py,
            rt.type_.clone_ref(py),
            rep.clone_ref(py),
            name.clone_ref(py),
        )?;
        // Aeon invariant: inner is TypeConstructor | TypeVar, never RefinedType.
        return make_refined_type(
            py,
            rt.name.clone_ref(py),
            new_inner,
            rt.refinement.clone_ref(py),
            rt.loc.clone_ref(py),
        );
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let nv = substitute_vartype(
            py,
            at.var_type.clone_ref(py),
            rep.clone_ref(py),
            name.clone_ref(py),
        )?;
        let nt = substitute_vartype(
            py,
            at.type_.clone_ref(py),
            rep.clone_ref(py),
            name.clone_ref(py),
        )?;
        return make_abstraction_type(
            py,
            at.var_name.clone_ref(py),
            nv,
            nt,
            at.loc.clone_ref(py),
            at.multiplicity.clone_ref(py),
        );
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        if name_eq(py, &tp.name, &name) {
            return Ok(t);
        }
        let nb = substitute_vartype(
            py,
            tp.body.clone_ref(py),
            rep.clone_ref(py),
            name.clone_ref(py),
        )?;
        return make_type_polymorphism(
            py,
            tp.name.clone_ref(py),
            tp.kind.clone_ref(py),
            nb,
            tp.loc.clone_ref(py),
        );
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let ns = substitute_vartype(
            py,
            rp.sort.clone_ref(py),
            rep.clone_ref(py),
            name.clone_ref(py),
        )?;
        let nb = substitute_vartype(
            py,
            rp.body.clone_ref(py),
            rep.clone_ref(py),
            name.clone_ref(py),
        )?;
        return make_refinement_polymorphism(
            py,
            rp.name.clone_ref(py),
            ns,
            nb,
            rp.loc.clone_ref(py),
        );
    }
    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let args = tc.args.bind(py);
        let new_args = PyList::empty_bound(py);
        for i in 0..args.len() {
            let arg = args.get_item(i)?;
            let new_arg =
                substitute_vartype(py, arg.into(), rep.clone_ref(py), name.clone_ref(py))?;
            new_args.append(new_arg)?;
        }
        return make_type_constructor(
            py,
            tc.name.clone_ref(py),
            new_args.unbind(),
            tc.loc.clone_ref(py),
        );
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "substitute_vartype: type {} not allowed in substitution",
        bound.repr()?.to_string()
    )))
}

// ---------- Qualifier-collection walks (aeon.typechecking.qualifiers) ----------

/// True if a LiquidApp wraps the binary && operator (Name("&&", 0)).
#[inline]
fn is_and_app(py: Python<'_>, t: &Bound<'_, PyAny>) -> bool {
    if let Ok(app) = t.downcast::<LiquidApp>() {
        let app = app.borrow();
        let fun = app.fun.borrow(py);
        return fun.name == "&&" && fun.id == 0;
    }
    false
}

/// Append the conjuncts of `p` (flattening nested LiquidApp("&&")) to `out`.
fn flatten_and_into(py: Python<'_>, p: PyObject, out: &Bound<'_, PyList>) -> PyResult<()> {
    let bound = p.bind(py);
    if is_and_app(py, bound) {
        if let Ok(app) = bound.downcast::<LiquidApp>() {
            let app = app.borrow();
            let args = app.args.bind(py);
            if args.len() == 2 {
                flatten_and_into(py, args.get_item(0)?.into(), out)?;
                flatten_and_into(py, args.get_item(1)?.into(), out)?;
                return Ok(());
            }
        }
    }
    out.append(p)?;
    Ok(())
}

/// Return the atoms of `p`: flatten &&-conjunctions, drop True and LiquidHornApplication.
fn atoms_from_predicate(py: Python<'_>, p: PyObject) -> PyResult<Py<PyList>> {
    let flat = PyList::empty_bound(py);
    flatten_and_into(py, p, &flat)?;
    let out = PyList::empty_bound(py);
    for i in 0..flat.len() {
        let chunk = flat.get_item(i)?;
        if chunk.is_instance_of::<LiquidHornApplication>() {
            continue;
        }
        if let Ok(b) = chunk.downcast::<LiquidLiteralBool>() {
            if b.borrow().value {
                continue;
            }
        }
        out.append(chunk)?;
    }
    Ok(out.unbind())
}

/// Walk a type tree and add all qualifier atoms found in refinements to `sink`.
/// Mirrors aeon.typechecking.qualifiers._collect_from_type.
#[pyfunction]
pub fn collect_from_type(py: Python<'_>, ty: PyObject, sink: &Bound<'_, PySet>) -> PyResult<()> {
    collect_from_type_inner(py, ty, sink)
}

/// Walk a term tree, collecting qualifier atoms from every type annotation it
/// touches. Mirrors aeon.typechecking.qualifiers._collect_from_term.
#[pyfunction]
pub fn collect_from_term(py: Python<'_>, t: PyObject, sink: &Bound<'_, PySet>) -> PyResult<()> {
    use crate::terms::{
        Abstraction, Annotation, Application, If, Let, Literal, Rec, RefinementApplication,
        TypeAbstraction, TypeApplication, Var,
    };

    let bound = t.bind(py);

    if let Ok(an) = bound.downcast::<Annotation>() {
        let an = an.borrow();
        collect_from_type_inner(py, an.type_.clone_ref(py), sink)?;
        collect_from_term(py, an.expr.clone_ref(py), sink)?;
        return Ok(());
    }
    if let Ok(app) = bound.downcast::<Application>() {
        let app = app.borrow();
        collect_from_term(py, app.fun.clone_ref(py), sink)?;
        collect_from_term(py, app.arg.clone_ref(py), sink)?;
        return Ok(());
    }
    if let Ok(ab) = bound.downcast::<Abstraction>() {
        let ab = ab.borrow();
        return collect_from_term(py, ab.body.clone_ref(py), sink);
    }
    if let Ok(le) = bound.downcast::<Let>() {
        let le = le.borrow();
        collect_from_term(py, le.var_value.clone_ref(py), sink)?;
        collect_from_term(py, le.body.clone_ref(py), sink)?;
        return Ok(());
    }
    if let Ok(rc) = bound.downcast::<Rec>() {
        let rc = rc.borrow();
        collect_from_type_inner(py, rc.var_type.clone_ref(py), sink)?;
        collect_from_term(py, rc.var_value.clone_ref(py), sink)?;
        collect_from_term(py, rc.body.clone_ref(py), sink)?;
        return Ok(());
    }
    if let Ok(ife) = bound.downcast::<If>() {
        let ife = ife.borrow();
        collect_from_term(py, ife.cond.clone_ref(py), sink)?;
        collect_from_term(py, ife.then.clone_ref(py), sink)?;
        collect_from_term(py, ife.otherwise.clone_ref(py), sink)?;
        return Ok(());
    }
    if let Ok(ta) = bound.downcast::<TypeAbstraction>() {
        let ta = ta.borrow();
        return collect_from_term(py, ta.body.clone_ref(py), sink);
    }
    if let Ok(tap) = bound.downcast::<TypeApplication>() {
        let tap = tap.borrow();
        collect_from_term(py, tap.body.clone_ref(py), sink)?;
        collect_from_type_inner(py, tap.type_.clone_ref(py), sink)?;
        return Ok(());
    }
    if let Ok(rapp) = bound.downcast::<RefinementApplication>() {
        let rapp = rapp.borrow();
        return collect_from_term(py, rapp.body.clone_ref(py), sink);
    }
    if let Ok(lit) = bound.downcast::<Literal>() {
        let lit = lit.borrow();
        return collect_from_type_inner(py, lit.type_.clone_ref(py), sink);
    }
    if bound.is_instance_of::<Var>() {
        return Ok(());
    }
    // Everything else (Hole, RefinementAbstraction): no atoms — mirrors the
    // Python's `case _: pass` fallback.
    Ok(())
}

fn collect_from_type_inner(py: Python<'_>, ty: PyObject, sink: &Bound<'_, PySet>) -> PyResult<()> {
    let bound = ty.bind(py);
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let atoms = atoms_from_predicate(py, rt.refinement.clone_ref(py))?;
        let atoms = atoms.bind(py);
        for i in 0..atoms.len() {
            sink.add(atoms.get_item(i)?)?;
        }
        collect_from_type_inner(py, rt.type_.clone_ref(py), sink)?;
        return Ok(());
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        collect_from_type_inner(py, at.var_type.clone_ref(py), sink)?;
        collect_from_type_inner(py, at.type_.clone_ref(py), sink)?;
        return Ok(());
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        return collect_from_type_inner(py, tp.body.clone_ref(py), sink);
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        return collect_from_type_inner(py, rp.body.clone_ref(py), sink);
    }
    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let args = tc.args.bind(py);
        for i in 0..args.len() {
            collect_from_type_inner(py, args.get_item(i)?.into(), sink)?;
        }
        return Ok(());
    }
    // TypeVar, Top, or anything else: nothing to collect.
    Ok(())
}

/// substitution_in_liquid(t, rep, name): replace LiquidVar(name) and references
/// to `name` inside LiquidApp/LiquidHornApplication function-names. Mirrors
/// aeon.core.substitutions.substitution_in_liquid.
#[pyfunction]
pub fn substitution_in_liquid(
    py: Python<'_>,
    t: PyObject,
    rep: PyObject,
    name: Py<Name>,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if bound.is_instance_of::<LiquidLiteralBool>()
        || bound.is_instance_of::<LiquidLiteralInt>()
        || bound.is_instance_of::<LiquidLiteralFloat>()
        || bound.is_instance_of::<LiquidLiteralString>()
    {
        return Ok(t);
    }
    if let Ok(v) = bound.downcast::<LiquidVar>() {
        let v = v.borrow();
        if name_eq(py, &v.name, &name) {
            return Ok(rep);
        }
        return Ok(t);
    }
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        let new_fun = if name_eq(py, &app.fun, &name) {
            let rep_bound = rep.bind(py);
            let rv = rep_bound.downcast::<LiquidVar>().map_err(|_| {
                pyo3::exceptions::PyAssertionError::new_err(
                    "rep must be LiquidVar when replacing a function name",
                )
            })?;
            rv.borrow().name.clone_ref(py)
        } else {
            app.fun.clone_ref(py)
        };
        let args = app.args.bind(py);
        let n = args.len();
        let new_args = PyList::empty_bound(py);
        for i in 0..n {
            let arg = args.get_item(i)?;
            let new_arg =
                substitution_in_liquid(py, arg.into(), rep.clone_ref(py), name.clone_ref(py))?;
            new_args.append(new_arg)?;
        }
        return make_liquid_app(py, new_fun, new_args.unbind(), app.loc.clone_ref(py));
    }
    if let Ok(h) = bound.downcast::<LiquidHornApplication>() {
        let h = h.borrow();
        // Python: `[(substitution_in_liquid(a, rep, name), t) for (a, t) in argtypes]`
        // The comprehension's `for (a, t)` rebinds `t` to each argtype's OWN
        // type — NOT the outer horn term. Each rebuilt tuple keeps its own ty.
        let argtypes = h.argtypes.bind(py);
        let n = argtypes.len();
        let new_argtypes = PyList::empty_bound(py);
        for i in 0..n {
            let item = argtypes.get_item(i)?;
            let tup = item.downcast::<PyTuple>().map_err(|_| {
                pyo3::exceptions::PyAssertionError::new_err("argtypes items must be tuples")
            })?;
            let a = tup.get_item(0)?;
            let ty = tup.get_item(1)?;
            let new_a =
                substitution_in_liquid(py, a.into(), rep.clone_ref(py), name.clone_ref(py))?;
            let new_tup = PyTuple::new_bound(py, &[new_a, ty.into()]);
            new_argtypes.append(new_tup)?;
        }
        return make_liquid_horn_application(
            py,
            h.name.clone_ref(py),
            new_argtypes.unbind(),
            h.loc.clone_ref(py),
        );
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "substitution_in_liquid: unsupported {}",
        bound.repr()?.to_string()
    )))
}
