//! Sugar-level type substitution / type-variable instantiation.
//! Port of `aeon.elaboration.instantiation`.
//!
//! These operate on the *sugar* type hierarchy (SType), distinct from the
//! core-type substitutions in `crate::substitutions`.

use pyo3::prelude::*;

use crate::name::Name;
use crate::sugar::{
    SAbstractionType, SRefinedType, SRefinementPolymorphism, STypeConstructor, STypePolymorphism,
    STypeVar, SType,
};
use crate::sugar_helpers::normalize;

/// Walk an SType, replacing every `STypeVar(alpha)` with `beta`. Internal
/// helper that takes an optional `alpha` (None = match by id-and-name).
fn type_substitution_inner(
    py: Python<'_>,
    ty: PyObject,
    alpha: &Py<Name>,
    beta: &PyObject,
    by_name_only: bool,
) -> PyResult<PyObject> {
    let ty = normalize(py, ty)?;
    let b = ty.bind(py);

    // STypeVar
    if let Ok(stv) = b.downcast::<STypeVar>() {
        let stv = stv.borrow();
        let stv_name = stv.name.bind(py).borrow();
        let alpha_b = alpha.bind(py).borrow();
        let matches = if by_name_only {
            stv_name.name == alpha_b.name
        } else {
            stv_name.name == alpha_b.name && stv_name.id == alpha_b.id
        };
        drop(stv_name);
        drop(alpha_b);
        drop(stv);
        if matches {
            return Ok(beta.clone_ref(py));
        }
        return Ok(ty);
    }

    // SRefinedType: substitute inside, then re-normalize.
    if let Ok(srt) = b.downcast::<SRefinedType>() {
        let srt = srt.borrow();
        let name = srt.name.clone_ref(py);
        let inner = srt.type_.clone_ref(py);
        let refn = srt.refinement.clone_ref(py);
        let loc = srt.loc.clone_ref(py);
        drop(srt);
        let new_inner = type_substitution_inner(py, inner, alpha, beta, by_name_only)?;
        let new_srt = Py::new(
            py,
            (
                SRefinedType { name, type_: new_inner, refinement: refn, loc },
                SType,
            ),
        )?
        .into_any();
        return normalize(py, new_srt);
    }

    // SAbstractionType
    if let Ok(sat) = b.downcast::<SAbstractionType>() {
        let sat = sat.borrow();
        let var_name = sat.var_name.clone_ref(py);
        let vty = sat.var_type.clone_ref(py);
        let rty = sat.type_.clone_ref(py);
        let loc = sat.loc.clone_ref(py);
        let mult = sat.multiplicity.clone_ref(py);
        drop(sat);
        let new_vty = type_substitution_inner(py, vty, alpha, beta, by_name_only)?;
        let new_rty = type_substitution_inner(py, rty, alpha, beta, by_name_only)?;
        return Ok(Py::new(
            py,
            (
                SAbstractionType {
                    var_name,
                    var_type: new_vty,
                    type_: new_rty,
                    loc,
                    multiplicity: mult,
                },
                SType,
            ),
        )?
        .into_any());
    }

    // STypePolymorphism (skips body if it binds alpha)
    if let Ok(stp) = b.downcast::<STypePolymorphism>() {
        let stp = stp.borrow();
        let stp_name = stp.name.bind(py).borrow();
        let alpha_b = alpha.bind(py).borrow();
        let same = if by_name_only {
            stp_name.name == alpha_b.name
        } else {
            stp_name.name == alpha_b.name && stp_name.id == alpha_b.id
        };
        drop(stp_name);
        drop(alpha_b);
        if same {
            drop(stp);
            return Ok(ty);
        }
        let name = stp.name.clone_ref(py);
        let kind = stp.kind.clone_ref(py);
        let body = stp.body.clone_ref(py);
        let loc = stp.loc.clone_ref(py);
        drop(stp);
        let new_body = type_substitution_inner(py, body, alpha, beta, by_name_only)?;
        return Ok(Py::new(
            py,
            (
                STypePolymorphism { name, kind, body: new_body, loc },
                SType,
            ),
        )?
        .into_any());
    }

    // SRefinementPolymorphism
    if let Ok(srp) = b.downcast::<SRefinementPolymorphism>() {
        let srp = srp.borrow();
        let name = srp.name.clone_ref(py);
        let sort = srp.sort.clone_ref(py);
        let body = srp.body.clone_ref(py);
        let loc = srp.loc.clone_ref(py);
        drop(srp);
        let new_sort = type_substitution_inner(py, sort, alpha, beta, by_name_only)?;
        let new_body = type_substitution_inner(py, body, alpha, beta, by_name_only)?;
        return Ok(Py::new(
            py,
            (
                SRefinementPolymorphism { name, sort: new_sort, body: new_body, loc },
                SType,
            ),
        )?
        .into_any());
    }

    // STypeConstructor
    if let Ok(stc) = b.downcast::<STypeConstructor>() {
        let stc = stc.borrow();
        let name = stc.name.clone_ref(py);
        let loc = stc.loc.clone_ref(py);
        let args = stc.args.clone_ref(py);
        drop(stc);
        let args_b = args.bind(py);
        let py_list = pyo3::types::PyList::empty_bound(py);
        let len = args_b.len();
        for i in 0..len {
            let item = args_b.get_item(i)?.unbind();
            let new_item = type_substitution_inner(py, item, alpha, beta, by_name_only)?;
            py_list.append(new_item)?;
        }
        return Ok(Py::new(
            py,
            (
                STypeConstructor { name, args: py_list.unbind(), loc },
                SType,
            ),
        )?
        .into_any());
    }

    // Fallback: return unchanged.
    Ok(ty)
}

/// t[alpha := beta]: standard capture-avoiding type substitution on sugar
/// types. Mirrors `aeon.elaboration.instantiation.type_substitution`.
#[pyfunction]
pub fn sugar_type_substitution(
    py: Python<'_>,
    ty: PyObject,
    alpha: Py<Name>,
    beta: PyObject,
) -> PyResult<PyObject> {
    type_substitution_inner(py, ty, &alpha, &beta, false)
}

/// t[alpha |-> beta]: type-variable instantiation. The original Python uses
/// `name == alpha` where alpha is a `str` (the user-facing name), comparing
/// the type-var's *name* part only. We replicate that behaviour by matching
/// on name only.
#[pyfunction]
pub fn sugar_type_variable_instantiation(
    py: Python<'_>,
    ty: PyObject,
    alpha: Py<Name>,
    beta: PyObject,
) -> PyResult<PyObject> {
    type_substitution_inner(py, ty, &alpha, &beta, true)
}
