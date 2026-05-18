//! Entailment under a typing context (port of `aeon.typechecking.entailment`).
//!
//! `entailment_context` lifts every binder in the typing context into the
//! Horn constraint as the right kind of declaration; `entailment` then
//! solves the lifted constraint with the qualifier atoms extracted from
//! the same context.

use pyo3::prelude::*;
use pyo3::types::PyList;

use crate::builders::{
    new_implication, new_liquid_var, new_reflected_function_declaration, new_type_constructor,
    new_uninterpreted_function_declaration,
};
use crate::name::Name;
use crate::substitutions::substitution_in_liquid;
use crate::typectx::{
    ReflectedBinder, TypeBinder, TypeConstructorBinder, TypingContext, UninterpretedBinder,
    VariableBinder,
};
use crate::types::{AbstractionType, RefinementPolymorphism, TypeConstructor, TypePolymorphism};

fn extract_parts_call(py: Python<'_>, ty: PyObject) -> PyResult<(Py<Name>, PyObject, PyObject)> {
    let core = py.import_bound("aeon.core.types")?;
    let func = core.getattr("extract_parts")?;
    let tup = func.call1((ty,))?;
    let tup_b = tup.downcast::<pyo3::types::PyTuple>()?;
    let nm: Py<Name> = tup_b.get_item(0)?.downcast::<Name>()?.clone().unbind();
    let base: PyObject = tup_b.get_item(1)?.unbind();
    let cond: PyObject = tup_b.get_item(2)?.unbind();
    Ok((nm, base, cond))
}

/// Returns whether a function name is one of the built-in `liquid_prelude`
/// operators. The prelude is Python-side data (~30 entries); we mirror the
/// names here to avoid a dict lookup per binder.
fn is_op_name(n: &str) -> bool {
    matches!(
        n,
        "==" | "!=" | "<" | "<=" | ">" | ">=" | "-->" | "&&" | "||" | "+" | "-" | "*" | "/"
            | "%" | "!" | "Set_sng" | "Set_cup" | "Set_cap" | "Set_dif" | "Set_mem" | "Set_sub"
    )
}

#[pyfunction]
pub fn entailment_context(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    mut c: PyObject,
) -> PyResult<PyObject> {
    let ctx_b = ctx.borrow();
    let entries = ctx_b.entries.clone_ref(py);
    drop(ctx_b);
    let entries_b = entries.bind(py);

    for i in (0..entries_b.len()).rev() {
        let entry = entries_b.get_item(i)?;

        if let Ok(vb) = entry.downcast::<VariableBinder>() {
            let vb = vb.borrow();
            let name = vb.name.clone_ref(py);
            let ty = vb.type_.clone_ref(py);
            drop(vb);
            let ty_b = ty.bind(py);

            // AbstractionType arm
            if ty_b.is_instance_of::<AbstractionType>() {
                let nm = name.borrow(py);
                if is_op_name(&nm.name) {
                    // operator binders are skipped (already in scope)
                    drop(nm);
                } else {
                    drop(nm);
                    if crate::sub::is_first_order_function(py, ty.clone_ref(py))? {
                        c = new_uninterpreted_function_declaration(py, name, ty, c)?;
                    }
                }
                continue;
            }
            // Polymorphism arms — operator skip, otherwise no-op
            if ty_b.is_instance_of::<TypePolymorphism>()
                || ty_b.is_instance_of::<RefinementPolymorphism>()
            {
                continue;
            }
            // base / refined arm
            let (nname, base, cond) = extract_parts_call(py, ty.clone_ref(py))?;
            let lv = new_liquid_var(py, name.clone_ref(py), crate::loc::default_location(py))?;
            let ncond = substitution_in_liquid(py, cond, lv, nname)?;
            let base_b = base.bind(py);
            if let Ok(tc) = base_b.downcast::<TypeConstructor>() {
                let tc = tc.borrow();
                let args = tc.args.bind(py);
                if args.len() == 0 {
                    drop(tc);
                    c = new_implication(py, name, base, ncond, c, None)?;
                    continue;
                }
                drop(tc);
                // Polymorphic constructor: erase to Int.
                let int_name = Py::new(py, Name { name: "Int".to_string(), id: 0 })?;
                let empty = PyList::empty_bound(py).unbind();
                let int_tc =
                    new_type_constructor(py, int_name, empty, crate::loc::default_location(py))?;
                c = new_implication(py, name, int_tc, ncond, c, None)?;
                continue;
            }
            // TypeVar arm
            if base_b.is_instance_of::<crate::types::TypeVar>() {
                c = new_implication(py, name, base, ncond, c, None)?;
                continue;
            }
            return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                "Unknown base: {}",
                base_b.repr()?.to_string()
            )));
        }

        if entry.downcast::<TypeBinder>().is_ok() {
            continue;
        }

        if let Ok(ub) = entry.downcast::<UninterpretedBinder>() {
            let ub = ub.borrow();
            let name = ub.name.clone_ref(py);
            let ty = ub.type_.clone_ref(py);
            drop(ub);
            c = new_uninterpreted_function_declaration(py, name, ty, c)?;
            continue;
        }

        if let Ok(rb) = entry.downcast::<ReflectedBinder>() {
            let rb = rb.borrow();
            let name = rb.name.clone_ref(py);
            let ty = rb.type_.clone_ref(py);
            let params = rb.params.clone_ref(py);
            let body = rb.body.clone_ref(py);
            drop(rb);
            c = new_reflected_function_declaration(py, name, ty, params, body, c)?;
            continue;
        }

        if entry.downcast::<TypeConstructorBinder>().is_ok() {
            continue;
        }

        return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "Untreated {}",
            entry.repr()?.to_string()
        )));
    }
    Ok(c)
}

#[pyfunction]
pub fn entailment(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    c: PyObject,
) -> PyResult<bool> {
    let lifted = entailment_context(py, ctx, c)?;
    let atoms = crate::qualifiers::extract_qualifier_atoms(py, ctx, None, None, 512)?;
    let ctx_obj: PyObject = ctx.clone().unbind().into_any();
    crate::horn::solve(py, lifted, Some(ctx_obj), Some(atoms.into_any()))
}
