//! Pretty-printer for core types and terms.
//! Port of `aeon.core.pprint`.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};
use std::sync::OnceLock;

use crate::liquid::LiquidLiteralBool;
use crate::terms::{
    Abstraction, Annotation, Application, Hole, If, Let, Literal, Rec, RefinementAbstraction,
    RefinementApplication, Term, TypeAbstraction, TypeApplication, Var,
};
use crate::types::{AbstractionType, RefinedType, TypeConstructor, TypeVar};

/// Mapping from operator name → ASCII identifier used to mangle bound names
/// in `custom_preludes_ops_representation`.
fn ops_table() -> &'static [(&'static str, &'static str)] {
    &[
        ("%", "mod"),
        ("/", "div"),
        ("*", "mul"),
        ("-", "sub"),
        ("+", "add"),
        ("%.", "modf"),
        ("/.", "divf"),
        ("*.", "mulf"),
        ("-.", "subf"),
        ("+.", "addf"),
        (">=", "gte"),
        (">", "gt"),
        ("<=", "lte"),
        ("<", "lt"),
        ("!=", "ne"),
        ("==", "eq"),
        ("&&", "and"),
        ("||", "or"),
        ("!", "not"),
    ]
}

fn op_text(op: &str) -> Option<&'static str> {
    ops_table().iter().find(|(o, _)| *o == op).map(|(_, t)| *t)
}

/// Build the module-level `aeon_prelude_ops_to_text` dict.
fn build_ops_dict(py: Python<'_>) -> PyResult<Py<PyDict>> {
    let d = PyDict::new_bound(py);
    for (k, v) in ops_table() {
        d.set_item(k, v)?;
    }
    Ok(d.unbind())
}

static OPS_DICT: OnceLock<Py<PyDict>> = OnceLock::new();

#[pyfunction]
pub fn get_aeon_prelude_ops_to_text(py: Python<'_>) -> Py<PyDict> {
    OPS_DICT
        .get_or_init(|| build_ops_dict(py).expect("aeon_prelude_ops_to_text build"))
        .clone_ref(py)
}

// ---- pretty_print (type) -------------------------------------------------

fn type_free_term_vars(py: Python<'_>, ty: &PyObject) -> PyResult<Vec<Py<crate::name::Name>>> {
    let core = py.import_bound("aeon.core.types")?;
    let result = core.getattr("type_free_term_vars")?.call1((ty,))?;
    let lst = result.downcast::<PyList>()?;
    let mut out = Vec::with_capacity(lst.len());
    for i in 0..lst.len() {
        let item = lst.get_item(i)?;
        let n: Py<crate::name::Name> = item.downcast::<crate::name::Name>()?.clone().unbind();
        out.push(n);
    }
    Ok(out)
}

/// `pretty_print(ty)` — render a core Type, hiding `True` refinements
/// and dropping argument names when the parameter is unused in the body.
#[pyfunction]
pub fn pretty_print(py: Python<'_>, t: PyObject) -> PyResult<String> {
    let b = t.bind(py);
    if b.downcast::<TypeConstructor>().is_ok() || b.downcast::<TypeVar>().is_ok() {
        return Ok(b.str()?.to_string());
    }
    if let Ok(at) = b.downcast::<AbstractionType>() {
        let at = at.borrow();
        let vn = at.var_name.clone_ref(py);
        let vt = at.var_type.clone_ref(py);
        let rt = at.type_.clone_ref(py);
        drop(at);
        let at_s = pretty_print(py, vt.clone_ref(py))?;
        let rt_s = pretty_print(py, rt)?;
        let frees = type_free_term_vars(py, &vt)?;
        let vn_b = vn.borrow(py);
        let vn_used = frees.iter().any(|f| {
            let f = f.borrow(py);
            f.name == vn_b.name && f.id == vn_b.id
        });
        if vn_used {
            return Ok(format!(
                "(\n                {}:{}) -> {}",
                vn_b.__str__(),
                at_s,
                rt_s
            ));
        }
        return Ok(format!("{} -> {}", at_s, rt_s));
    }
    if let Ok(rt) = b.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let inner = rt.type_.clone_ref(py);
        let it_s = pretty_print(py, inner)?;
        let ref_b = rt.refinement.bind(py);
        if let Ok(llb) = ref_b.downcast::<LiquidLiteralBool>() {
            if llb.borrow().value {
                return Ok(it_s);
            }
        }
        let n = rt.name.borrow(py).__str__();
        let ref_s = ref_b.str()?.to_string();
        return Ok(format!("{{{}:{} | {}}}", n, it_s, ref_s));
    }
    Err(pyo3::exceptions::PyValueError::new_err(format!(
        "Unknown type {}",
        b.str()?
    )))
}

// ---- operator_name -------------------------------------------------------

/// If `term` is a (possibly type-applied) operator variable, return its name.
fn operator_name(py: Python<'_>, term: PyObject) -> PyResult<Option<String>> {
    let mut inner = term;
    loop {
        let b = inner.bind(py);
        match b.downcast::<TypeApplication>() {
            Ok(ta) => {
                let body = ta.borrow().body.clone_ref(py);
                inner = body;
            }
            Err(_) => break,
        }
    }
    let b = inner.bind(py);
    if let Ok(v) = b.downcast::<Var>() {
        let v = v.borrow();
        let n = v.name.borrow(py);
        let nname = n.name.clone();
        drop(n);
        drop(v);
        if op_text(&nname).is_some() {
            return Ok(Some(nname));
        }
    }
    Ok(None)
}

#[pyfunction(name = "operator_name")]
pub fn py_operator_name(py: Python<'_>, term: PyObject) -> PyResult<Option<String>> {
    operator_name(py, term)
}

// ---- custom_preludes_ops_representation ---------------------------------

fn cpor(
    py: Python<'_>,
    term: PyObject,
    counter: i64,
) -> PyResult<(String, i64)> {
    let b = term.bind(py);

    // Application case — handle binary/unary operator pretty-printing.
    if let Ok(app) = b.downcast::<Application>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        drop(app);

        // Try fully-applied binary operator: ((op left) right) -> (left op right)
        let fun_b = fun.bind(py);
        if let Ok(inner_app) = fun_b.downcast::<Application>() {
            let inner_app = inner_app.borrow();
            let opfun = inner_app.fun.clone_ref(py);
            let left = inner_app.arg.clone_ref(py);
            drop(inner_app);
            let op = operator_name(py, opfun)?;
            if let Some(op) = op.clone() {
                if op != "!" {
                    let (left_s, c1) = cpor(py, left, counter)?;
                    let (right_s, c2) = cpor(py, arg, c1)?;
                    return Ok((format!("({} {} {})", left_s, op, right_s), c2));
                }
            }
        }

        // Try unary `!`: (! arg)
        let op = operator_name(py, fun.clone_ref(py))?;
        if let Some(opn) = op.clone() {
            if opn == "!" {
                let (arg_s, c1) = cpor(py, arg, counter)?;
                return Ok((format!("(!{})", arg_s), c1));
            }
            // Partial binary operator: (op left) -> (\v -> left op v)
            let (left_s, c1) = cpor(py, arg, counter)?;
            let counter = c1 + 1;
            let txt = op_text(&opn).unwrap_or(&opn);
            let new_var = format!("__{}_{}__", txt, counter);
            return Ok((
                format!("(\\{} -> {} {} {})", new_var, left_s, opn, new_var),
                counter,
            ));
        }

        // Plain application: (fun arg)
        let (fun_s, c1) = cpor(py, fun, counter)?;
        let (arg_s, c2) = cpor(py, arg, c1)?;
        return Ok((format!("({} {})", fun_s, arg_s), c2));
    }

    if let Ok(ann) = b.downcast::<Annotation>() {
        let ann = ann.borrow();
        let expr = ann.expr.clone_ref(py);
        let ty = ann.type_.clone_ref(py);
        drop(ann);
        let (expr_s, c1) = cpor(py, expr, counter)?;
        let ty_s = ty.bind(py).str()?.to_string();
        return Ok((format!("({} : {})", expr_s, ty_s), c1));
    }

    if let Ok(abs) = b.downcast::<Abstraction>() {
        let abs = abs.borrow();
        let vn = abs.var_name.borrow(py).__str__();
        let body = abs.body.clone_ref(py);
        drop(abs);
        let (body_s, c1) = cpor(py, body, counter)?;
        return Ok((format!("(\\{} -> {})", vn, body_s), c1));
    }

    if let Ok(lt) = b.downcast::<Let>() {
        let lt = lt.borrow();
        let vn = lt.var_name.borrow(py).__str__();
        let vv = lt.var_value.clone_ref(py);
        let body = lt.body.clone_ref(py);
        drop(lt);
        let (vv_s, c1) = cpor(py, vv, counter)?;
        let (body_s, c2) = cpor(py, body, c1)?;
        return Ok((format!("(let {} = {} in\n {})", vn, vv_s, body_s), c2));
    }

    if let Ok(rec) = b.downcast::<Rec>() {
        let rec = rec.borrow();
        let vn = rec.var_name.borrow(py).__str__();
        let vt = rec.var_type.bind(py).str()?.to_string();
        let vv = rec.var_value.clone_ref(py);
        let body = rec.body.clone_ref(py);
        drop(rec);
        let (vv_s, c1) = cpor(py, vv, counter)?;
        let (body_s, c2) = cpor(py, body, c1)?;
        return Ok((
            format!("(let {} : {} = {} in\n {})", vn, vt, vv_s, body_s),
            c2,
        ));
    }

    if let Ok(iff) = b.downcast::<If>() {
        let iff = iff.borrow();
        let c = iff.cond.clone_ref(py);
        let t = iff.then.clone_ref(py);
        let e = iff.otherwise.clone_ref(py);
        drop(iff);
        let (c_s, c1) = cpor(py, c, counter)?;
        let (t_s, c2) = cpor(py, t, c1)?;
        let (e_s, c3) = cpor(py, e, c2)?;
        return Ok((format!("(if {} then {} else {})", c_s, t_s, e_s), c3));
    }

    if let Ok(ta) = b.downcast::<TypeAbstraction>() {
        let ta = ta.borrow();
        let n = ta.name.borrow(py).__str__();
        let k = ta.kind.bind(py).str()?.to_string();
        let body = ta.body.clone_ref(py);
        drop(ta);
        let (body_s, c1) = cpor(py, body, counter)?;
        return Ok((format!("ƛ{}:{}.({})", n, k, body_s), c1));
    }

    if let Ok(ra) = b.downcast::<RefinementAbstraction>() {
        let ra = ra.borrow();
        let n = ra.name.borrow(py).__str__();
        let s = ra.sort.bind(py).str()?.to_string();
        let body = ra.body.clone_ref(py);
        drop(ra);
        let (body_s, c1) = cpor(py, body, counter)?;
        return Ok((format!("Λρ{}:({}).({})", n, s, body_s), c1));
    }

    if let Ok(tap) = b.downcast::<TypeApplication>() {
        let tap = tap.borrow();
        let body = tap.body.clone_ref(py);
        let ty = tap.type_.bind(py).str()?.to_string();
        drop(tap);
        let (body_s, c1) = cpor(py, body, counter)?;
        return Ok((format!("({})[{}]", body_s, ty), c1));
    }

    if let Ok(rap) = b.downcast::<RefinementApplication>() {
        let rap = rap.borrow();
        let body = rap.body.clone_ref(py);
        let refn = rap.refinement.clone_ref(py);
        drop(rap);
        let (body_s, c1) = cpor(py, body, counter)?;
        let (ref_s, c2) = cpor(py, refn, c1)?;
        return Ok((format!("({})[{{{}}}]", body_s, ref_s), c2));
    }

    if b.downcast::<Literal>().is_ok()
        || b.downcast::<Var>().is_ok()
        || b.downcast::<Hole>().is_ok()
    {
        return Ok((b.str()?.to_string(), counter));
    }

    // Fallback for anything else: just the default str().
    Ok((b.str()?.to_string(), counter))
}

#[pyfunction]
#[pyo3(signature = (term, counter = 0))]
pub fn custom_preludes_ops_representation(
    py: Python<'_>,
    term: PyObject,
    counter: i64,
) -> PyResult<(String, i64)> {
    cpor(py, term, counter)
}

#[pyfunction]
pub fn pretty_print_term(py: Python<'_>, term: PyObject) -> PyResult<()> {
    let (s, _) = cpor(py, term, 0)?;
    println!("{}", s);
    Ok(())
}

// silence unused
#[allow(dead_code)]
fn _force_term(_t: Term) {}
