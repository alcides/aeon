//! Qualifier atom extraction (port of `aeon.typechecking.qualifiers`).
//!
//! Used by predicate abstraction / constrained Horn solving: unknown
//! refinements are searched as boolean combinations of atoms drawn from
//! this finite set Q.

use pyo3::prelude::*;
use pyo3::types::{PyFrozenSet, PyList, PySet};

use crate::substitutions::{collect_from_term, collect_from_type};
use crate::typectx::{TypingContext, UninterpretedBinder, VariableBinder};

#[pyfunction]
#[pyo3(signature = (ctx, goal_type = None, term = None, max_atoms = 512))]
pub fn extract_qualifier_atoms(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    goal_type: Option<PyObject>,
    term: Option<PyObject>,
    max_atoms: usize,
) -> PyResult<Py<PyFrozenSet>> {
    let sink = PySet::empty_bound(py)?;

    let ctx_b = ctx.borrow();
    let entries = ctx_b.entries.bind(py);
    for i in 0..entries.len() {
        let e = entries.get_item(i)?;
        if let Ok(vb) = e.downcast::<VariableBinder>() {
            let ty = vb.borrow().type_.clone_ref(py);
            collect_from_type(py, ty, &sink)?;
        } else if let Ok(ub) = e.downcast::<UninterpretedBinder>() {
            let ty = ub.borrow().type_.clone_ref(py);
            collect_from_type(py, ty, &sink)?;
        }
    }
    drop(ctx_b);

    if let Some(gt) = goal_type {
        collect_from_type(py, gt, &sink)?;
    }
    if let Some(t) = term {
        collect_from_term(py, t, &sink)?;
    }

    if sink.len() <= max_atoms {
        // frozenset(sink)
        let elems = PyList::empty_bound(py);
        for item in sink.iter() {
            elems.append(item)?;
        }
        let items: Vec<PyObject> = elems.iter().map(|x| x.unbind()).collect();
        return Ok(PyFrozenSet::new_bound(py, items.iter())?.unbind());
    }

    // Deterministic truncation: sort by repr, take the first max_atoms.
    let mut items_with_repr: Vec<(String, PyObject)> = Vec::with_capacity(sink.len());
    for item in sink.iter() {
        let r = item.repr()?.to_string();
        items_with_repr.push((r, item.unbind()));
    }
    items_with_repr.sort_by(|a, b| a.0.cmp(&b.0));
    items_with_repr.truncate(max_atoms);
    let elems = PyList::empty_bound(py);
    for (_, item) in items_with_repr {
        elems.append(item)?;
    }
    let items: Vec<PyObject> = elems.iter().map(|x| x.unbind()).collect();
    Ok(PyFrozenSet::new_bound(py, items.iter())?.unbind())
}
