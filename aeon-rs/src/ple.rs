//! PLE (Proof by Logical Evaluation) unfolding from aeon.verification.smt.
//!
//! `ple_unfold_fixpoint` repeatedly inlines reflected-function applications
//! in a LiquidTerm until a fixpoint (or a guard) is reached. It's invoked
//! once per premise and once per conclusion in `flatten`, and showed up
//! heavily in compile-time profiling.
//!
//! This is the z3-free slice of the SMT encoder — pure LiquidTerm rewriting.
//! The z3-touching `translate` / `smt_valid` path remains in Python.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};
use std::collections::HashSet;

use crate::builders::new_liquid_app;
use crate::liquid::LiquidApp;
use crate::name::Name;
use crate::substitutions::substitution_in_liquid;

/// One PLE step. Returns (new_term, changed).
///
/// Mirrors aeon.verification.smt._ple_unfold_once: recurse into LiquidApp
/// args; if the application head is a reflected function with a matching
/// arity, inline its body with the args substituted for the params.
fn ple_unfold_once(
    py: Python<'_>,
    t: PyObject,
    reflected: &Bound<'_, PyDict>,
) -> PyResult<(PyObject, bool)> {
    let bound = t.bind(py);
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        let args = app.args.bind(py);
        let n_args = PyList::empty_bound(py);
        let mut changed = false;
        for i in 0..args.len() {
            let arg = args.get_item(i)?;
            let (n_arg, arg_changed) = ple_unfold_once(py, arg.into(), reflected)?;
            n_args.append(n_arg)?;
            changed = changed || arg_changed;
        }
        // key = str(fun)
        let key = app.fun.borrow(py).__str__();
        if let Some(entry) = reflected.get_item(&key)? {
            let tup = entry.downcast::<PyTuple>().map_err(|_| {
                pyo3::exceptions::PyTypeError::new_err("reflected_functions value must be a tuple")
            })?;
            let params = tup.get_item(0)?;
            let params = params.downcast::<PyTuple>().map_err(|_| {
                pyo3::exceptions::PyTypeError::new_err("reflected_functions params must be a tuple")
            })?;
            if params.len() == n_args.len() {
                let mut unfolded: PyObject = tup.get_item(1)?.into();
                for j in 0..params.len() {
                    let param: Py<Name> = params.get_item(j)?.extract()?;
                    let arg: PyObject = n_args.get_item(j)?.into();
                    unfolded = substitution_in_liquid(py, unfolded, arg, param)?;
                }
                return Ok((unfolded, true));
            }
        }
        if changed {
            let r = new_liquid_app(
                py,
                app.fun.clone_ref(py),
                n_args.unbind(),
                app.loc.clone_ref(py),
            )?;
            return Ok((r, true));
        }
        return Ok((t, false));
    }
    Ok((t, false))
}

/// term_size: 1 + sum of children sizes for LiquidApp, else 1.
fn term_size(py: Python<'_>, node: &Bound<'_, PyAny>) -> PyResult<usize> {
    if let Ok(app) = node.downcast::<LiquidApp>() {
        let app = app.borrow();
        let args = app.args.bind(py);
        let mut s = 1usize;
        for i in 0..args.len() {
            s += term_size(py, &args.get_item(i)?)?;
        }
        Ok(s)
    } else {
        Ok(1)
    }
}

/// Repeatedly apply ple_unfold_once until no change, a size guard, a
/// seen-before guard, or max_steps. Mirrors smt.ple_unfold_fixpoint.
///
/// The Python original emits a `logger.debug` line per call; that's
/// intentionally dropped — it's debug-level and has no observable effect.
#[pyfunction]
#[pyo3(signature = (t, reflected_functions, max_steps = 256))]
pub fn ple_unfold_fixpoint(
    py: Python<'_>,
    t: PyObject,
    reflected_functions: &Bound<'_, PyDict>,
    max_steps: usize,
) -> PyResult<PyObject> {
    const MAX_TERM_SIZE: usize = 4096;

    let mut current = t;
    let mut seen: HashSet<String> = HashSet::new();
    seen.insert(current.bind(py).repr()?.to_string());

    for _ in 0..max_steps {
        let (next, changed) = ple_unfold_once(py, current, reflected_functions)?;
        current = next;
        if !changed {
            break;
        }
        if term_size(py, current.bind(py))? > MAX_TERM_SIZE {
            break;
        }
        let signature = current.bind(py).repr()?.to_string();
        if seen.contains(&signature) {
            break;
        }
        seen.insert(signature);
    }
    Ok(current)
}
