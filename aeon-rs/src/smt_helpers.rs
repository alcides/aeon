//! Pure (z3-free) helper walks from aeon.verification.smt:
//!
//!  - unrefine_type   (Type -> Type)   strip refinements everywhere
//!  - uncurry         (AbstractionType -> ([TypeConstructor], TypeConstructor))
//!
//! These feed make_variable / mk_funs (which stay in Python because they
//! build z3 objects). Porting them here removes the recursive Python walks
//! from the hot encoding path without pulling in z3.

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::builders::{
    new_abstraction_type, new_type_constructor, new_type_polymorphism,
};
use crate::name::Name;
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, TypeConstructor, TypePolymorphism,
    TypeVar,
};

/// A fresh `TypeConstructor(Name(name, 0), [])` — mirrors aeon.core.types.t_*.
fn base_tc(py: Python<'_>, name: &str) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: name.to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    let loc = crate::loc::default_location(py);
    new_type_constructor(py, n, empty, loc)
}

/// unrefine_type: drop refinements throughout a type.
/// Mirrors aeon.verification.smt.unrefine_type.
#[pyfunction]
pub fn unrefine_type(py: Python<'_>, base: PyObject) -> PyResult<PyObject> {
    let bound = base.bind(py);

    if let Ok(rt) = bound.downcast::<RefinedType>() {
        return Ok(rt.borrow().type_.clone_ref(py));
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let nv = unrefine_type(py, at.var_type.clone_ref(py))?;
        let nt = unrefine_type(py, at.type_.clone_ref(py))?;
        return new_abstraction_type(py, at.var_name.clone_ref(py), nv, nt, at.loc.clone_ref(py));
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let nb = unrefine_type(py, tp.body.clone_ref(py))?;
        return new_type_polymorphism(py, tp.name.clone_ref(py), tp.kind.clone_ref(py), nb, tp.loc.clone_ref(py));
    }
    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let args = tc.args.bind(py);
        let new_args = PyList::empty_bound(py);
        for i in 0..args.len() {
            let a = args.get_item(i)?;
            new_args.append(unrefine_type(py, a.into())?)?;
        }
        return new_type_constructor(py, tc.name.clone_ref(py), new_args.unbind(), tc.loc.clone_ref(py));
    }
    // Top, TypeVar, anything else: returned as-is.
    Ok(base)
}

/// uncurry: flatten an AbstractionType into (input base types, output type),
/// collapsing higher-rank / type-constructor arguments to scalar tokens.
/// Mirrors aeon.verification.smt.uncurry.
#[pyfunction]
pub fn uncurry<'py>(py: Python<'py>, base: PyObject) -> PyResult<Bound<'py, PyTuple>> {
    let mut current = unrefine_type(py, base.clone_ref(py))?;
    let inputs = PyList::empty_bound(py);
    let mut vars_to_remove: Vec<(String, i64)> = Vec::new();

    // Peel TypePolymorphism wrappers, recording bound type-var names.
    loop {
        let cur = current.bind(py);
        if let Ok(tp) = cur.downcast::<TypePolymorphism>() {
            let tp = tp.borrow();
            {
                let n = tp.name.borrow(py);
                vars_to_remove.push((n.name.clone(), n.id));
            }
            let body = tp.body.clone_ref(py);
            drop(tp);
            current = body;
        } else {
            break;
        }
    }

    // Walk the AbstractionType spine, classifying each var_type.
    loop {
        let cur = current.bind(py);
        let at = match cur.downcast::<AbstractionType>() {
            Ok(at) => at,
            Err(_) => break,
        };
        let at = at.borrow();
        let vt = at.var_type.bind(py);

        if let Ok(tc) = vt.downcast::<TypeConstructor>() {
            if tc.borrow().args.bind(py).len() == 0 {
                // TypeConstructor(_, []) — keep as-is
                inputs.append(at.var_type.clone_ref(py))?;
            } else {
                // TypeConstructor(_, non-empty) — scalar token
                inputs.append(base_tc(py, "Int")?)?;
            }
        } else if vt.is_instance_of::<Top>() {
            inputs.append(base_tc(py, "Unit")?)?;
        } else if let Ok(tvar) = vt.downcast::<TypeVar>() {
            let tvar = tvar.borrow();
            let n = tvar.name.borrow(py);
            let bound_here = vars_to_remove.iter().any(|(nm, id)| *nm == n.name && *id == n.id);
            if bound_here {
                inputs.append(base_tc(py, "Int")?)?;
            } else {
                // TypeConstructor(name)
                let nm = tvar.name.clone_ref(py);
                let empty = PyList::empty_bound(py).unbind();
                let loc = crate::loc::default_location(py);
                inputs.append(new_type_constructor(py, nm, empty, loc)?)?;
            }
        } else if vt.is_instance_of::<AbstractionType>()
            || vt.is_instance_of::<TypePolymorphism>()
            || vt.is_instance_of::<RefinementPolymorphism>()
        {
            inputs.append(base_tc(py, "Int")?)?;
        } else {
            return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                "uncurry: unknown SMT type {}",
                vt.repr()?.to_string()
            )));
        }

        let next = at.type_.clone_ref(py);
        drop(at);
        current = next;
    }

    // Output type: Top collapses to Unit; must end at a TypeConstructor.
    let out = {
        let cur = current.bind(py);
        if cur.is_instance_of::<Top>() {
            base_tc(py, "Unit")?
        } else if cur.is_instance_of::<TypeConstructor>() {
            current.clone_ref(py)
        } else {
            return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                "uncurry: unknown SMT output type {}",
                cur.repr()?.to_string()
            )));
        }
    };

    Ok(PyTuple::new_bound(py, &[inputs.into_any().unbind(), out]))
}
