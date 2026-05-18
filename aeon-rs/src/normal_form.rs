//! A-normal-form / partial-evaluation pass over the core AST.
//! Port of `aeon.optimization.normal_form`.
//!
//! `nf` does one step of normalisation; `normal_form` iterates `nf` to a
//! fixpoint. The cases:
//! - Beta reduction: `(\x -> body) arg` → `body[arg/x]` (plus the
//!   annotation-wrapped variant).
//! - Type-level beta: `(Λa:κ. body)[ty]` → `body[ty/a]`.
//! - If on a literal Bool.
//! - Constant folding + identity / absorbent / same-operand peephole
//!   simplifications for `+ - * / % && || == != < <= > >=`.
//! - Let-elimination via substitution.

use pyo3::prelude::*;

use crate::name::Name;
use crate::terms::{
    Abstraction, Annotation, Application, Hole, If, Let, Literal, Rec, Term, TypeAbstraction,
    TypeApplication, Var,
};
use crate::types::{Type, TypeConstructor};
use crate::term_subst::{substitute_vartype_in_term, substitution};

fn mk_int(py: Python<'_>) -> PyResult<PyObject> {
    let name = Py::new(py, Name { name: "Int".to_string(), id: 0 })?;
    Ok(Py::new(
        py,
        (
            TypeConstructor {
                name,
                args: pyo3::types::PyList::empty_bound(py).unbind(),
                loc: crate::loc::default_location(py),
            },
            Type,
        ),
    )?
    .into_any())
}

fn mk_bool(py: Python<'_>) -> PyResult<PyObject> {
    let name = Py::new(py, Name { name: "Bool".to_string(), id: 0 })?;
    Ok(Py::new(
        py,
        (
            TypeConstructor {
                name,
                args: pyo3::types::PyList::empty_bound(py).unbind(),
                loc: crate::loc::default_location(py),
            },
            Type,
        ),
    )?
    .into_any())
}

/// `Var` matching name `n` (any id)?
fn var_named(py: Python<'_>, t: &PyObject, n: &str) -> bool {
    let Ok(v) = t.bind(py).downcast::<Var>() else {
        return false;
    };
    let v = v.borrow();
    let nm = v.name.borrow(py);
    nm.name == n
}

/// Build a literal of the given Python value with type `ty`.
fn lit(py: Python<'_>, value: PyObject, ty: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(
        py,
        (
            Literal { value, type_: ty, loc: crate::loc::default_location(py) },
            Term,
        ),
    )?
    .into_any())
}

/// True iff t is `Literal(v, _)` with `v == target` (Python equality).
fn lit_value_eq(py: Python<'_>, t: &PyObject, target: &PyObject) -> PyResult<bool> {
    let Ok(l) = t.bind(py).downcast::<Literal>() else {
        return Ok(false);
    };
    let l = l.borrow();
    Ok(l.value.bind(py).eq(target.bind(py))?)
}

/// True iff t is `Literal(_, ty)` where ty is `Bool`-like; returns the bool.
fn as_bool_lit(py: Python<'_>, t: &PyObject) -> PyResult<Option<bool>> {
    let Ok(l) = t.bind(py).downcast::<Literal>() else {
        return Ok(None);
    };
    let l = l.borrow();
    if let Ok(b) = l.value.extract::<bool>(py) {
        return Ok(Some(b));
    }
    Ok(None)
}

/// Try to extract `(op_name, left, right)` if `t` is the curried application
/// `((Var(op) left) right)`.
fn as_binop(
    py: Python<'_>,
    t: &PyObject,
) -> PyResult<Option<(String, PyObject, PyObject)>> {
    let Ok(outer) = t.bind(py).downcast::<Application>() else {
        return Ok(None);
    };
    let outer = outer.borrow();
    let outer_fun = outer.fun.clone_ref(py);
    let right = outer.arg.clone_ref(py);
    drop(outer);

    let Ok(inner) = outer_fun.bind(py).downcast::<Application>() else {
        return Ok(None);
    };
    let inner = inner.borrow();
    let inner_fun = inner.fun.clone_ref(py);
    let left = inner.arg.clone_ref(py);
    drop(inner);

    let Ok(v) = inner_fun.bind(py).downcast::<Var>() else {
        return Ok(None);
    };
    let v = v.borrow();
    let op = v.name.borrow(py).name.clone();
    drop(v);

    Ok(Some((op, left, right)))
}

/// True iff two terms are equal by Python `__eq__`.
fn term_eq(py: Python<'_>, a: &PyObject, b: &PyObject) -> PyResult<bool> {
    a.bind(py).eq(b.bind(py))
}

/// One step of normal-form reduction.
fn nf(py: Python<'_>, t: PyObject) -> PyResult<PyObject> {
    let tb = t.bind(py);

    // --- Beta reduction: ((\x -> body) arg) -> body[arg/x]
    if let Ok(app) = tb.downcast::<Application>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        drop(app);

        // (\x -> body) arg
        if let Ok(abs) = fun.bind(py).downcast::<Abstraction>() {
            let abs = abs.borrow();
            let var_name = abs.var_name.clone_ref(py);
            let body = abs.body.clone_ref(py);
            drop(abs);
            return substitution(py, body, arg, var_name);
        }

        // ((\x -> body) : ty) arg
        if let Ok(ann) = fun.bind(py).downcast::<Annotation>() {
            let ann = ann.borrow();
            let inner = ann.expr.clone_ref(py);
            drop(ann);
            if let Ok(abs) = inner.bind(py).downcast::<Abstraction>() {
                let abs = abs.borrow();
                let var_name = abs.var_name.clone_ref(py);
                let body = abs.body.clone_ref(py);
                drop(abs);
                return substitution(py, body, arg, var_name);
            }
        }
    }

    // --- Type-level beta: (Λa:κ. body)[ty] -> body[ty/a]
    if let Ok(ta) = tb.downcast::<TypeApplication>() {
        let ta = ta.borrow();
        let body_obj = ta.body.clone_ref(py);
        let ty = ta.type_.clone_ref(py);
        drop(ta);
        if let Ok(tab) = body_obj.bind(py).downcast::<TypeAbstraction>() {
            let tab = tab.borrow();
            let vty = tab.name.clone_ref(py);
            let body = tab.body.clone_ref(py);
            drop(tab);
            return substitute_vartype_in_term(py, body, ty, vty);
        }
    }

    // --- If on a Bool literal
    if let Ok(iff) = tb.downcast::<If>() {
        let iff = iff.borrow();
        let cond = iff.cond.clone_ref(py);
        let then = iff.then.clone_ref(py);
        let otherwise = iff.otherwise.clone_ref(py);
        let loc = iff.loc.clone_ref(py);
        drop(iff);

        if let Some(b) = as_bool_lit(py, &cond)? {
            return Ok(if b { then } else { otherwise });
        }
        // Fall through to recurse into the subterms.
        let nc = nf(py, cond)?;
        let nt = nf(py, then)?;
        let no = nf(py, otherwise)?;
        return Ok(Py::new(
            py,
            (If { cond: nc, then: nt, otherwise: no, loc }, Term),
        )?
        .into_any());
    }

    // --- Binary-operator simplifications
    if let Some((op, left, right)) = as_binop(py, &t)? {
        let py_true = pyo3::types::PyBool::new_bound(py, true).to_owned().into_any().unbind();
        let py_false = pyo3::types::PyBool::new_bound(py, false).to_owned().into_any().unbind();

        match op.as_str() {
            "&&" => {
                // && True e -> e ; && False e -> False ; && e True -> e ; && e False -> False
                if lit_value_eq(py, &left, &py_true)? {
                    return Ok(right);
                }
                if lit_value_eq(py, &left, &py_false)? {
                    return Ok(left);
                }
                if lit_value_eq(py, &right, &py_true)? {
                    return Ok(left);
                }
                if lit_value_eq(py, &right, &py_false)? {
                    return Ok(right);
                }
            }
            "||" => {
                if lit_value_eq(py, &left, &py_true)? {
                    return Ok(left);
                }
                if lit_value_eq(py, &left, &py_false)? {
                    return Ok(right);
                }
                if lit_value_eq(py, &right, &py_true)? {
                    return Ok(right);
                }
                if lit_value_eq(py, &right, &py_false)? {
                    return Ok(left);
                }
            }
            "+" => {
                let py_zero = 0_i64.into_py(py);
                if lit_value_eq(py, &left, &py_zero)? {
                    return Ok(right);
                }
                if lit_value_eq(py, &right, &py_zero)? {
                    return Ok(left);
                }
                // const + const
                if let (Some(a), Some(b)) =
                    (extract_int(py, &left)?, extract_int(py, &right)?)
                {
                    return lit(py, (a + b).into_py(py), mk_int(py)?);
                }
            }
            "-" => {
                let py_zero = 0_i64.into_py(py);
                if lit_value_eq(py, &right, &py_zero)? {
                    return Ok(left);
                }
                if let (Some(a), Some(b)) =
                    (extract_int(py, &left)?, extract_int(py, &right)?)
                {
                    return lit(py, (a - b).into_py(py), mk_int(py)?);
                }
                if term_eq(py, &left, &right)? {
                    return lit(py, 0_i64.into_py(py), mk_int(py)?);
                }
            }
            "*" => {
                let py_zero = 0_i64.into_py(py);
                let py_one = 1_i64.into_py(py);
                if lit_value_eq(py, &left, &py_zero)? {
                    return Ok(left);
                }
                if lit_value_eq(py, &right, &py_zero)? {
                    return Ok(right);
                }
                if lit_value_eq(py, &left, &py_one)? {
                    return Ok(right);
                }
                if lit_value_eq(py, &right, &py_one)? {
                    return Ok(left);
                }
                if let (Some(a), Some(b)) =
                    (extract_int(py, &left)?, extract_int(py, &right)?)
                {
                    return lit(py, (a * b).into_py(py), mk_int(py)?);
                }
            }
            "/" => {
                let py_zero = 0_i64.into_py(py);
                if lit_value_eq(py, &left, &py_zero)? {
                    return Ok(left);
                }
                if term_eq(py, &left, &right)? {
                    return lit(py, 1_i64.into_py(py), mk_int(py)?);
                }
            }
            "%" => {
                let py_zero = 0_i64.into_py(py);
                if lit_value_eq(py, &left, &py_zero)? {
                    return lit(py, 0_i64.into_py(py), mk_int(py)?);
                }
                if term_eq(py, &left, &right)? {
                    return lit(py, 0_i64.into_py(py), mk_int(py)?);
                }
            }
            "==" => {
                if let (Some(a), Some(b)) =
                    (extract_int(py, &left)?, extract_int(py, &right)?)
                {
                    return lit(py, (a == b).into_py(py), mk_bool(py)?);
                }
            }
            "!=" => {
                if let (Some(a), Some(b)) =
                    (extract_int(py, &left)?, extract_int(py, &right)?)
                {
                    return lit(py, (a != b).into_py(py), mk_bool(py)?);
                }
            }
            ">" => {
                if let (Some(a), Some(b)) =
                    (extract_int(py, &left)?, extract_int(py, &right)?)
                {
                    return lit(py, (a > b).into_py(py), mk_bool(py)?);
                }
            }
            ">=" => {
                if let (Some(a), Some(b)) =
                    (extract_int(py, &left)?, extract_int(py, &right)?)
                {
                    return lit(py, (a >= b).into_py(py), mk_bool(py)?);
                }
            }
            "<" => {
                if let (Some(a), Some(b)) =
                    (extract_int(py, &left)?, extract_int(py, &right)?)
                {
                    return lit(py, (a < b).into_py(py), mk_bool(py)?);
                }
            }
            "<=" => {
                if let (Some(a), Some(b)) =
                    (extract_int(py, &left)?, extract_int(py, &right)?)
                {
                    return lit(py, (a <= b).into_py(py), mk_bool(py)?);
                }
            }
            _ => {}
        }
    }

    // --- Leaves
    if tb.downcast::<Literal>().is_ok()
        || tb.downcast::<Var>().is_ok()
        || tb.downcast::<Annotation>().is_ok()
        || tb.downcast::<Hole>().is_ok()
    {
        return Ok(t);
    }

    // --- Recursive cases
    if let Ok(abs) = tb.downcast::<Abstraction>() {
        let abs = abs.borrow();
        let var_name = abs.var_name.clone_ref(py);
        let body = abs.body.clone_ref(py);
        let loc = abs.loc.clone_ref(py);
        drop(abs);
        let nbody = nf(py, body)?;
        return Ok(Py::new(
            py,
            (Abstraction { var_name, body: nbody, loc }, Term),
        )?
        .into_any());
    }

    if let Ok(app) = tb.downcast::<Application>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        let loc = app.loc.clone_ref(py);
        drop(app);
        let nfun = nf(py, fun)?;
        let narg = nf(py, arg)?;
        return Ok(Py::new(
            py,
            (Application { fun: nfun, arg: narg, loc }, Term),
        )?
        .into_any());
    }

    if let Ok(lt) = tb.downcast::<Let>() {
        let lt = lt.borrow();
        let var_name = lt.var_name.clone_ref(py);
        let var_value = lt.var_value.clone_ref(py);
        let body = lt.body.clone_ref(py);
        drop(lt);
        let nv = nf(py, var_value)?;
        return substitution(py, body, nv, var_name);
    }

    if let Ok(rec) = tb.downcast::<Rec>() {
        let rec = rec.borrow();
        let var_name = rec.var_name.clone_ref(py);
        let var_type = rec.var_type.clone_ref(py);
        let var_value = rec.var_value.clone_ref(py);
        let body = rec.body.clone_ref(py);
        let decreasing_by = rec.decreasing_by.clone_ref(py);
        let loc = rec.loc.clone_ref(py);
        let mult = rec.multiplicity.clone_ref(py);
        drop(rec);
        let nv = nf(py, var_value)?;
        let nb = nf(py, body)?;
        return Ok(Py::new(
            py,
            (
                Rec {
                    var_name,
                    var_type,
                    var_value: nv,
                    body: nb,
                    decreasing_by,
                    loc,
                    multiplicity: mult,
                },
                Term,
            ),
        )?
        .into_any());
    }

    if let Ok(tab) = tb.downcast::<TypeAbstraction>() {
        let tab = tab.borrow();
        let name = tab.name.clone_ref(py);
        let kind = tab.kind.clone_ref(py);
        let body = tab.body.clone_ref(py);
        let loc = tab.loc.clone_ref(py);
        drop(tab);
        let nb = nf(py, body)?;
        return Ok(Py::new(
            py,
            (TypeAbstraction { name, kind, body: nb, loc }, Term),
        )?
        .into_any());
    }

    if let Ok(ta) = tb.downcast::<TypeApplication>() {
        let ta = ta.borrow();
        let body = ta.body.clone_ref(py);
        let ty = ta.type_.clone_ref(py);
        let loc = ta.loc.clone_ref(py);
        drop(ta);
        let nb = nf(py, body)?;
        return Ok(Py::new(
            py,
            (TypeApplication { body: nb, type_: ty, loc }, Term),
        )?
        .into_any());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "No case for {} ({})",
        tb.str()?,
        tb.get_type().name()?
    )))
}

fn extract_int(py: Python<'_>, t: &PyObject) -> PyResult<Option<i64>> {
    let Ok(l) = t.bind(py).downcast::<Literal>() else {
        return Ok(None);
    };
    let l = l.borrow();
    if let Ok(b) = l.value.extract::<bool>(py) {
        let _ = b; // bool extracts as int in Python; we don't want that
        if l.value.bind(py).is_instance_of::<pyo3::types::PyBool>() {
            return Ok(None);
        }
    }
    Ok(l.value.extract::<i64>(py).ok())
}

/// Iterate `nf` to a fixpoint.
#[pyfunction]
pub fn normal_form(py: Python<'_>, t: PyObject) -> PyResult<PyObject> {
    let mut cur = t;
    loop {
        let nt = nf(py, cur.clone_ref(py))?;
        if cur.bind(py).eq(nt.bind(py))? {
            return Ok(nt);
        }
        cur = nt;
    }
}

/// Alias matching the Python API.
#[pyfunction]
pub fn optimize(py: Python<'_>, t: PyObject) -> PyResult<PyObject> {
    normal_form(py, t)
}

#[pyfunction(name = "nf")]
pub fn py_nf(py: Python<'_>, t: PyObject) -> PyResult<PyObject> {
    nf(py, t)
}
