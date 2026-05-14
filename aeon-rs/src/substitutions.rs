//! Rust ports of aeon.core.instantiation.type_substitution and
//! aeon.core.substitutions.substitution_in_liquid. These are the two
//! recursive walks the profiler flagged as hottest in synthesis.

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidVar,
};
use crate::name::Name;
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, TypeConstructor, TypePolymorphism,
    TypeVar,
};

#[inline]
fn name_eq(py: Python<'_>, a: &Py<Name>, b: &Py<Name>) -> bool {
    let a = a.borrow(py);
    let b = b.borrow(py);
    a.id == b.id && a.name == b.name
}

#[inline]
fn name_eq_obj(py: Python<'_>, a: &Py<Name>, b: PyObject) -> bool {
    if let Ok(b) = b.downcast_bound::<Name>(py) {
        let a = a.borrow(py);
        let b = b.borrow();
        a.id == b.id && a.name == b.name
    } else {
        false
    }
}

/// type_substitution(t, alpha, beta): replace all TypeVar(alpha) occurrences
/// in `t` with `beta`. Mirrors aeon.core.instantiation.type_substitution.
#[pyfunction]
pub fn type_substitution(py: Python<'_>, t: PyObject, alpha: Py<Name>, beta: PyObject) -> PyResult<PyObject> {
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
        // Recursively substitute in inner; in the common case inner is a
        // TypeConstructor or TypeVar (not refined), and we just rebuild.
        let new_inner = type_substitution(py, rt.type_.clone_ref(py), alpha.clone_ref(py), beta.clone_ref(py))?;
        let new_inner_bound = new_inner.bind(py);

        // If substitution produced another RefinedType, we'd need to merge
        // refinements (and-them). For PR 1 we delegate that edge case to the
        // existing Python implementation by importing.
        if new_inner_bound.is_instance_of::<RefinedType>() {
            // Delegate to Python — rare case, correctness over perf.
            let py_inst = py.import_bound("aeon.core.instantiation")?;
            let ts = py_inst.getattr("type_substitution_py_fallback")?;
            return ts.call1((t, alpha, beta))?.extract();
        }
        if new_inner_bound.is_instance_of::<AbstractionType>() {
            return Err(pyo3::exceptions::PyAssertionError::new_err(
                "Abstraction types cannot be refined",
            ));
        }
        let cls = py.import_bound("aeon_rs")?.getattr("RefinedType")?;
        let result = cls.call1((
            rt.name.clone_ref(py),
            new_inner,
            rt.refinement.clone_ref(py),
            rt.loc.clone_ref(py),
        ))?;
        return Ok(result.into());
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let new_var_type =
            type_substitution(py, at.var_type.clone_ref(py), alpha.clone_ref(py), beta.clone_ref(py))?;
        let new_type =
            type_substitution(py, at.type_.clone_ref(py), alpha.clone_ref(py), beta.clone_ref(py))?;
        let cls = py.import_bound("aeon_rs")?.getattr("AbstractionType")?;
        let result = cls.call1((
            at.var_name.clone_ref(py),
            new_var_type,
            new_type,
            at.loc.clone_ref(py),
        ))?;
        return Ok(result.into());
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        if name_eq(py, &tp.name, &alpha) {
            return Ok(t);
        }
        let new_body =
            type_substitution(py, tp.body.clone_ref(py), alpha.clone_ref(py), beta.clone_ref(py))?;
        let cls = py.import_bound("aeon_rs")?.getattr("TypePolymorphism")?;
        let result = cls.call1((
            tp.name.clone_ref(py),
            tp.kind.clone_ref(py),
            new_body,
            tp.loc.clone_ref(py),
        ))?;
        return Ok(result.into());
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let new_sort =
            type_substitution(py, rp.sort.clone_ref(py), alpha.clone_ref(py), beta.clone_ref(py))?;
        let new_body =
            type_substitution(py, rp.body.clone_ref(py), alpha.clone_ref(py), beta.clone_ref(py))?;
        let cls = py.import_bound("aeon_rs")?.getattr("RefinementPolymorphism")?;
        let result = cls.call1((
            rp.name.clone_ref(py),
            new_sort,
            new_body,
            rp.loc.clone_ref(py),
        ))?;
        return Ok(result.into());
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
        let cls = py.import_bound("aeon_rs")?.getattr("TypeConstructor")?;
        let result = cls.call1((tc.name.clone_ref(py), new_args, tc.loc.clone_ref(py)))?;
        return Ok(result.into());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "type_substitution: unknown type {}",
        bound.repr()?.to_string()
    )))
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
        // If fun name matches `name`, the rep must be a LiquidVar; replace fun.
        let new_fun = if name_eq(py, &app.fun, &name) {
            let rep_bound = rep.bind(py);
            let rv = rep_bound
                .downcast::<LiquidVar>()
                .map_err(|_| pyo3::exceptions::PyAssertionError::new_err(
                    "rep must be LiquidVar when replacing a function name",
                ))?;
            rv.borrow().name.clone_ref(py)
        } else {
            app.fun.clone_ref(py)
        };
        let args = app.args.bind(py);
        let n = args.len();
        let new_args = PyList::empty_bound(py);
        for i in 0..n {
            let arg = args.get_item(i)?;
            let new_arg = substitution_in_liquid(py, arg.into(), rep.clone_ref(py), name.clone_ref(py))?;
            new_args.append(new_arg)?;
        }
        let cls = py.import_bound("aeon_rs")?.getattr("LiquidApp")?;
        let result = cls.call1((new_fun, new_args, app.loc.clone_ref(py)))?;
        return Ok(result.into());
    }
    if let Ok(h) = bound.downcast::<LiquidHornApplication>() {
        let h = h.borrow();
        // NB: matches the Python: it uses `aname` (original) not the renamed
        // one to construct the new horn application. We mirror that quirk.
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
            let new_a = substitution_in_liquid(py, a.into(), rep.clone_ref(py), name.clone_ref(py))?;
            // Note: original Python passes `t` (the outer LiquidHornApplication!) as the type,
            // which is almost certainly a bug; we replicate the Python behavior verbatim.
            let _ = ty; // silence unused; replicates the (a, t) pattern from Python
            let new_tup = PyTuple::new_bound(py, &[new_a, t.clone_ref(py)]);
            new_argtypes.append(new_tup)?;
        }
        let cls = py.import_bound("aeon_rs")?.getattr("LiquidHornApplication")?;
        let result = cls.call1((h.name.clone_ref(py), new_argtypes, h.loc.clone_ref(py)))?;
        return Ok(result.into());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "substitution_in_liquid: unsupported {}",
        bound.repr()?.to_string()
    )))
}
