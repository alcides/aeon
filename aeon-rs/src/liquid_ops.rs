//! Port of `aeon.core.liquid_ops` — built-in operator type signatures and
//! short-circuiting AND/OR constructors over `LiquidTerm`.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};
use std::sync::OnceLock;

use crate::liquid::{LiquidApp, LiquidLiteralBool, LiquidTerm};
use crate::name::Name;
use crate::types::{Type, TypeConstructor, TypeVar};

fn mk_name(py: Python<'_>, s: &str) -> PyResult<Py<Name>> {
    Py::new(py, Name { name: s.to_string(), id: 0 })
}

fn mk_tc(py: Python<'_>, s: &str) -> PyResult<PyObject> {
    let name = mk_name(py, s)?;
    Ok(Py::new(
        py,
        (
            TypeConstructor { name, args: PyList::empty_bound(py).unbind(), loc: crate::loc::default_location(py) },
            Type,
        ),
    )?
    .into_any())
}

fn mk_tv(py: Python<'_>, s: &str) -> PyResult<PyObject> {
    let name = mk_name(py, s)?;
    Ok(Py::new(
        py,
        (TypeVar { name, loc: crate::loc::default_location(py) }, Type),
    )?
    .into_any())
}

fn build_prelude(py: Python<'_>) -> PyResult<Py<PyDict>> {
    let d = PyDict::new_bound(py);

    let t_bool = mk_tc(py, "Bool")?;
    let t_int = mk_tc(py, "Int")?;
    let t_set = mk_tc(py, "Set")?;

    // Helper to push (op, [signature]).
    let mut push = |op: &str, sig: Vec<PyObject>| -> PyResult<()> {
        let key = mk_name(py, op)?;
        let lst = PyList::empty_bound(py);
        for t in sig {
            lst.append(t)?;
        }
        d.set_item(key, lst)?;
        Ok(())
    };

    // Comparison: a -> a -> Bool. (a, a, Bool) for all of these.
    for op in ["==", "!=", "<", "<=", ">", ">="] {
        push(op, vec![mk_tv(py, "a")?, mk_tv(py, "a")?, t_bool.clone_ref(py)])?;
    }

    // Boolean: --> && || on Bool.
    for op in ["-->", "&&", "||"] {
        push(op, vec![t_bool.clone_ref(py), t_bool.clone_ref(py), t_bool.clone_ref(py)])?;
    }

    // Arithmetic: a -> a -> a.
    for op in ["+", "-", "*", "/"] {
        push(op, vec![mk_tv(py, "a")?, mk_tv(py, "a")?, mk_tv(py, "a")?])?;
    }

    // Int-specific.
    push("%", vec![t_int.clone_ref(py), t_int.clone_ref(py), t_int.clone_ref(py)])?;

    // Unary not on Bool.
    push("!", vec![t_bool.clone_ref(py), t_bool.clone_ref(py)])?;

    // SMT set operations.
    push("Set_sng", vec![t_int.clone_ref(py), t_set.clone_ref(py)])?;
    push("Set_cup", vec![t_set.clone_ref(py), t_set.clone_ref(py), t_set.clone_ref(py)])?;
    push("Set_cap", vec![t_set.clone_ref(py), t_set.clone_ref(py), t_set.clone_ref(py)])?;
    push("Set_dif", vec![t_set.clone_ref(py), t_set.clone_ref(py), t_set.clone_ref(py)])?;
    push("Set_mem", vec![t_int.clone_ref(py), t_set.clone_ref(py), t_bool.clone_ref(py)])?;
    push("Set_sub", vec![t_set.clone_ref(py), t_set.clone_ref(py), t_bool.clone_ref(py)])?;

    Ok(d.unbind())
}

static PRELUDE: OnceLock<Py<PyDict>> = OnceLock::new();

fn liquid_prelude_dict(py: Python<'_>) -> Py<PyDict> {
    PRELUDE
        .get_or_init(|| build_prelude(py).expect("liquid_prelude build"))
        .clone_ref(py)
}

/// Module-level `liquid_prelude: dict[Name, list[Type]]`.
#[pyfunction]
pub fn get_liquid_prelude(py: Python<'_>) -> Py<PyDict> {
    liquid_prelude_dict(py)
}

/// Short-circuiting AND over LiquidTerms.
#[pyfunction]
pub fn mk_liquid_and(py: Python<'_>, e1: PyObject, e2: PyObject) -> PyResult<PyObject> {
    let e1b = e1.bind(py);
    let e2b = e2.bind(py);
    if let Ok(b1) = e1b.downcast::<LiquidLiteralBool>() {
        if b1.borrow().value {
            return Ok(e2);
        }
        return Ok(e1);
    }
    if let Ok(b2) = e2b.downcast::<LiquidLiteralBool>() {
        if b2.borrow().value {
            return Ok(e1);
        }
        return Ok(e2);
    }
    let and_name = Py::new(py, Name { name: "&&".to_string(), id: 0 })?;
    let args = PyList::new_bound(py, &[e1, e2]).unbind();
    let app = Py::new(
        py,
        (LiquidApp { fun: and_name, args, loc: crate::loc::default_location(py) }, LiquidTerm),
    )?;
    Ok(app.into_any())
}

/// Short-circuiting OR over LiquidTerms.
#[pyfunction]
pub fn mk_liquid_or(py: Python<'_>, e1: PyObject, e2: PyObject) -> PyResult<PyObject> {
    let e1b = e1.bind(py);
    let e2b = e2.bind(py);
    if let Ok(b1) = e1b.downcast::<LiquidLiteralBool>() {
        if b1.borrow().value {
            return Ok(e1); // True
        }
        // e1 is False — result is e2.
        return Ok(e2);
    }
    if let Ok(b2) = e2b.downcast::<LiquidLiteralBool>() {
        if b2.borrow().value {
            return Ok(e2); // True
        }
        return Ok(e1);
    }
    let or_name = Py::new(py, Name { name: "||".to_string(), id: 0 })?;
    let args = PyList::new_bound(py, &[e1, e2]).unbind();
    let app = Py::new(
        py,
        (LiquidApp { fun: or_name, args, loc: crate::loc::default_location(py) }, LiquidTerm),
    )?;
    Ok(app.into_any())
}
