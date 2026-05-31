//! Type-walking helpers — port of the free functions in
//! `aeon.core.types`: `base`, `extract_parts`, `is_bare`,
//! `type_free_term_vars`, `get_type_vars`, `with_binders`.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PySet, PyTuple};

use crate::liquid::{LiquidHole, LiquidHornApplication, LiquidTerm};
use crate::name::Name;
use crate::types::{
    AbstractionType, ExistentialType, RefinedType, RefinementPolymorphism, Top, Type,
    TypeConstructor, TypePolymorphism, TypeVar,
};

/// `base(ty)` — strip a `RefinedType` wrapper to expose its inner type.
#[pyfunction]
pub fn base(py: Python<'_>, ty: PyObject) -> PyObject {
    if let Ok(rt) = ty.bind(py).downcast::<RefinedType>() {
        return rt.borrow().type_.clone_ref(py);
    }
    ty
}

/// `extract_parts(ty)` — pull `(name, base_type, refinement)` out of a
/// refined type. Bare `TypeConstructor` / `TypeVar` get a `_self` name
/// and a `LiquidLiteralBool(True)` refinement to match the Python
/// helper's contract.
#[pyfunction]
pub fn extract_parts(py: Python<'_>, t: PyObject) -> PyResult<(Py<Name>, PyObject, PyObject)> {
    let b = t.bind(py);
    if let Ok(rt) = b.downcast::<RefinedType>() {
        let rt = rt.borrow();
        return Ok((
            rt.name.clone_ref(py),
            rt.type_.clone_ref(py),
            rt.refinement.clone_ref(py),
        ));
    }
    if b.downcast::<TypeConstructor>().is_ok() || b.downcast::<TypeVar>().is_ok() {
        let n = Py::new(py, Name { name: "_self".to_string(), id: 0 })?;
        let liq_true = crate::builders::new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
        return Ok((n, t, liq_true));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "extract_parts: unsupported type {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

/// `is_bare(t)` — true iff `t` has no user-written refinement (only
/// `LiquidHole` / `LiquidHornApplication` placeholders, or no refinement
/// at all). Function types must be bare on every input/return.
#[pyfunction]
pub fn is_bare(py: Python<'_>, t: PyObject) -> PyResult<bool> {
    let b = t.bind(py);
    if b.downcast::<TypeConstructor>().is_ok()
        || b.downcast::<Top>().is_ok()
        || b.downcast::<TypeVar>().is_ok()
    {
        return Ok(true);
    }
    if let Ok(rt) = b.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let refb = rt.refinement.bind(py);
        return Ok(refb.downcast::<LiquidHole>().is_ok()
            || refb.downcast::<LiquidHornApplication>().is_ok());
    }
    if let Ok(at) = b.downcast::<AbstractionType>() {
        let at = at.borrow();
        let vt = at.var_type.clone_ref(py);
        let rt = at.type_.clone_ref(py);
        drop(at);
        return Ok(is_bare(py, vt)? && is_bare(py, rt)?);
    }
    if let Ok(tp) = b.downcast::<TypePolymorphism>() {
        let body = tp.borrow().body.clone_ref(py);
        return is_bare(py, body);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unknown type {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

/// Look up `ALL_OPS` from `aeon.prelude.prelude` and return the set of
/// strings. Cached per-call (called twice per `type_free_term_vars`
/// outermost invocation at most).
fn all_ops_set(py: Python<'_>) -> PyResult<std::collections::HashSet<String>> {
    let prelude = py.import_bound("aeon.prelude.prelude")?;
    let ops_obj = prelude.getattr("ALL_OPS")?;
    let ops_list = ops_obj.downcast::<PyList>()?;
    let mut out = std::collections::HashSet::with_capacity(ops_list.len());
    for i in 0..ops_list.len() {
        out.insert(ops_list.get_item(i)?.extract::<String>()?);
    }
    Ok(out)
}

fn name_in_ops(py: Python<'_>, name: &Py<Name>, ops: &std::collections::HashSet<String>) -> bool {
    ops.contains(&name.borrow(py).name)
}

fn name_eq(py: Python<'_>, a: &Py<Name>, b: &Py<Name>) -> bool {
    let a = a.borrow(py);
    let b = b.borrow(py);
    a.name == b.name && a.id == b.id
}

fn tftv_rec(
    py: Python<'_>,
    t: PyObject,
    ops: &std::collections::HashSet<String>,
) -> PyResult<Vec<Py<Name>>> {
    let b = t.bind(py);
    if b.downcast::<TypeConstructor>().is_ok() || b.downcast::<TypeVar>().is_ok() {
        return Ok(Vec::new());
    }
    if let Ok(at) = b.downcast::<AbstractionType>() {
        let at = at.borrow();
        let vt = at.var_type.clone_ref(py);
        let rt = at.type_.clone_ref(py);
        let bound = at.var_name.clone_ref(py);
        drop(at);
        let afv = tftv_rec(py, vt, ops)?;
        let rfv = tftv_rec(py, rt, ops)?;
        let mut out: Vec<Py<Name>> = Vec::with_capacity(afv.len() + rfv.len());
        for v in afv.into_iter().chain(rfv.into_iter()) {
            if name_eq(py, &v, &bound) {
                continue;
            }
            if name_in_ops(py, &v, ops) {
                continue;
            }
            out.push(v);
        }
        return Ok(out);
    }
    if let Ok(rt) = b.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let inner = rt.type_.clone_ref(py);
        let refn = rt.refinement.clone_ref(py);
        let bound = rt.name.clone_ref(py);
        drop(rt);
        let ifv = tftv_rec(py, inner, ops)?;
        let rfv_obj = crate::liquid::liquid_free_vars(py, refn)?;
        let rfv_b = rfv_obj.bind(py);
        let mut rfv: Vec<Py<Name>> = Vec::with_capacity(rfv_b.len());
        for i in 0..rfv_b.len() {
            let n: Py<Name> = rfv_b.get_item(i)?.downcast::<Name>()?.clone().unbind();
            rfv.push(n);
        }
        let mut out: Vec<Py<Name>> = Vec::with_capacity(ifv.len() + rfv.len());
        for v in ifv.into_iter().chain(rfv.into_iter()) {
            if !name_eq(py, &v, &bound) {
                out.push(v);
            }
        }
        return Ok(out);
    }
    if let Ok(tp) = b.downcast::<TypePolymorphism>() {
        let body = tp.borrow().body.clone_ref(py);
        return tftv_rec(py, body, ops);
    }
    if let Ok(rp) = b.downcast::<RefinementPolymorphism>() {
        let body = rp.borrow().body.clone_ref(py);
        return tftv_rec(py, body, ops);
    }
    if let Ok(et) = b.downcast::<ExistentialType>() {
        let et = et.borrow();
        let binders = et.binders.clone_ref(py);
        let body = et.body.clone_ref(py);
        drop(et);
        let binders_b = binders.bind(py);
        // binder_names
        let mut binder_names: Vec<Py<Name>> = Vec::with_capacity(binders_b.len());
        for i in 0..binders_b.len() {
            let tup = binders_b.get_item(i)?;
            let n: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            binder_names.push(n);
        }
        // walk binders accumulating their type's free vars, scoping each
        let mut bfv: Vec<Py<Name>> = Vec::new();
        let mut seen: Vec<Py<Name>> = Vec::new();
        for i in 0..binders_b.len() {
            let tup = binders_b.get_item(i)?;
            let bn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let bt = tup.get_item(1)?.unbind();
            for v in tftv_rec(py, bt, ops)? {
                if seen.iter().any(|s| name_eq(py, s, &v)) {
                    continue;
                }
                if name_in_ops(py, &v, ops) {
                    continue;
                }
                bfv.push(v);
            }
            seen.push(bn);
        }
        let body_fv = tftv_rec(py, body, ops)?;
        let mut out: Vec<Py<Name>> = Vec::with_capacity(bfv.len() + body_fv.len());
        for v in bfv.into_iter().chain(body_fv.into_iter()) {
            if binder_names.iter().any(|bn| name_eq(py, bn, &v)) {
                continue;
            }
            if name_in_ops(py, &v, ops) {
                continue;
            }
            out.push(v);
        }
        return Ok(out);
    }
    Ok(Vec::new())
}

/// Free term-level variables of a type (those not shadowed by a binder
/// and not part of the operator prelude `ALL_OPS`). Mirrors Python's
/// `type_free_term_vars` exactly, including the existential case.
#[pyfunction]
pub fn type_free_term_vars(py: Python<'_>, t: PyObject) -> PyResult<Py<PyList>> {
    let ops = all_ops_set(py)?;
    let out = tftv_rec(py, t, &ops)?;
    let lst = PyList::empty_bound(py);
    for v in out {
        lst.append(v)?;
    }
    Ok(lst.unbind())
}

/// `get_type_vars(t)` — collect the free TypeVar instances in a type,
/// stripping those bound by a `TypePolymorphism`.
#[pyfunction]
pub fn get_type_vars(py: Python<'_>, t: PyObject) -> PyResult<Py<PySet>> {
    let set = PySet::empty_bound(py)?;
    gtv_into(py, t, &set)?;
    Ok(set.unbind())
}

fn gtv_into(py: Python<'_>, t: PyObject, set: &Bound<'_, PySet>) -> PyResult<()> {
    let b = t.bind(py);
    if b.downcast::<TypeConstructor>().is_ok() {
        return Ok(());
    }
    if b.downcast::<TypeVar>().is_ok() {
        set.add(t)?;
        return Ok(());
    }
    if let Ok(at) = b.downcast::<AbstractionType>() {
        let at = at.borrow();
        let vt = at.var_type.clone_ref(py);
        let rt = at.type_.clone_ref(py);
        drop(at);
        gtv_into(py, vt, set)?;
        gtv_into(py, rt, set)?;
        return Ok(());
    }
    if let Ok(rt) = b.downcast::<RefinedType>() {
        let inner = rt.borrow().type_.clone_ref(py);
        return gtv_into(py, inner, set);
    }
    if let Ok(tp) = b.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let name = tp.name.clone_ref(py);
        let body = tp.body.clone_ref(py);
        drop(tp);
        // collect body's free vars, then remove any matching `name`
        let inner = PySet::empty_bound(py)?;
        gtv_into(py, body, &inner)?;
        let iter = inner.iter();
        for tv in iter {
            // tv is a TypeVar — check its name
            let tv_name = tv.getattr("name")?.downcast::<Name>()?.clone().unbind();
            let same = {
                let a = name.borrow(py);
                let b = tv_name.borrow(py);
                a.name == b.name && a.id == b.id
            };
            if !same {
                set.add(tv)?;
            }
        }
        return Ok(());
    }
    if let Ok(rp) = b.downcast::<RefinementPolymorphism>() {
        let body = rp.borrow().body.clone_ref(py);
        return gtv_into(py, body, set);
    }
    if let Ok(et) = b.downcast::<ExistentialType>() {
        let body = et.borrow().body.clone_ref(py);
        return gtv_into(py, body, set);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unable to extract {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

/// `with_binders(extra, ty)` — smart constructor that prepends a tuple
/// of `(Name, Type)` binders to `ty`, flattening any existing
/// `ExistentialType` so the result is at most one wrapper deep.
#[pyfunction]
pub fn with_binders(py: Python<'_>, extra: PyObject, ty: PyObject) -> PyResult<PyObject> {
    let extra_b = extra.bind(py);
    let extra_len = extra_b.len()?;
    if extra_len == 0 {
        return Ok(ty);
    }
    let b = ty.bind(py);
    if let Ok(et) = b.downcast::<ExistentialType>() {
        let et = et.borrow();
        let old_binders = et.binders.clone_ref(py);
        let body = et.body.clone_ref(py);
        let loc = et.loc.clone_ref(py);
        drop(et);
        // Concatenate (extra, old_binders) into a fresh tuple.
        let mut items: Vec<PyObject> = Vec::with_capacity(extra_len + old_binders.bind(py).len());
        for i in 0..extra_len {
            items.push(extra_b.get_item(i)?.unbind());
        }
        let old_b = old_binders.bind(py);
        for i in 0..old_b.len() {
            items.push(old_b.get_item(i)?.unbind());
        }
        let new_binders = PyTuple::new_bound(py, items).unbind();
        return Ok(Py::new(
            py,
            (ExistentialType { binders: new_binders, body, loc }, Type),
        )?
        .into_any());
    }
    // ty is not an ExistentialType — wrap it.
    let mut items: Vec<PyObject> = Vec::with_capacity(extra_len);
    for i in 0..extra_len {
        items.push(extra_b.get_item(i)?.unbind());
    }
    let new_binders = PyTuple::new_bound(py, items).unbind();
    let loc = match b.getattr("loc") {
        Ok(l) => l.unbind(),
        Err(_) => crate::loc::default_location(py),
    };
    Ok(Py::new(
        py,
        (
            ExistentialType { binders: new_binders, body: ty, loc },
            Type,
        ),
    )?
    .into_any())
}

// ---- Module-level constants -------------------------------------------------

fn mk_tc(py: Python<'_>, name: &str) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: name.to_string(), id: 0 })?;
    Ok(Py::new(
        py,
        (
            TypeConstructor {
                name: n,
                args: PyList::empty_bound(py).unbind(),
                loc: crate::loc::default_location(py),
            },
            Type,
        ),
    )?
    .into_any())
}

#[pyfunction]
pub fn get_t_unit(py: Python<'_>) -> PyResult<PyObject> {
    mk_tc(py, "Unit")
}
#[pyfunction]
pub fn get_t_bool(py: Python<'_>) -> PyResult<PyObject> {
    mk_tc(py, "Bool")
}
#[pyfunction]
pub fn get_t_int(py: Python<'_>) -> PyResult<PyObject> {
    mk_tc(py, "Int")
}
#[pyfunction]
pub fn get_t_float(py: Python<'_>) -> PyResult<PyObject> {
    mk_tc(py, "Float")
}
#[pyfunction]
pub fn get_t_string(py: Python<'_>) -> PyResult<PyObject> {
    mk_tc(py, "String")
}
#[pyfunction]
pub fn get_t_set(py: Python<'_>) -> PyResult<PyObject> {
    mk_tc(py, "Set")
}
#[pyfunction]
pub fn get_t_tensor(py: Python<'_>) -> PyResult<PyObject> {
    mk_tc(py, "Tensor")
}
#[pyfunction]
pub fn get_t_gpu_config(py: Python<'_>) -> PyResult<PyObject> {
    mk_tc(py, "GpuConfig")
}

#[pyfunction]
pub fn get_builtin_core_types(py: Python<'_>) -> PyResult<Py<PyList>> {
    let lst = PyList::empty_bound(py);
    for n in ["Unit", "Bool", "Int", "Float", "String", "Set", "Tensor", "GpuConfig"] {
        lst.append(mk_tc(py, n)?)?;
    }
    Ok(lst.unbind())
}

#[pyfunction]
pub fn get_top(py: Python<'_>) -> PyResult<PyObject> {
    Ok(Py::new(py, (Top, Type))?.into_any())
}

#[pyfunction]
pub fn get_liq_true(py: Python<'_>) -> PyResult<PyObject> {
    crate::builders::new_liquid_literal_bool(py, true, crate::loc::default_location(py))
}

// Silence unused-import warnings (LiquidTerm is referenced by the helpers
// transitively but not directly here).
#[allow(dead_code)]
fn _force_liquid_term(_t: LiquidTerm, _: &PyDict) {}
