//! Bidirectional refinement type checker (port of
//! `aeon.typechecking.typeinfer`).
//!
//! `synth(ctx, t)` infers the term's most precise refined type plus the
//! verification-condition constraint that needs to hold; `check(ctx, t, ty)`
//! generates the constraint that `t` has type `ty`. `check_type` runs both
//! plus the entailment closure and returns a bool. Errors from these
//! functions are raised as Python exceptions from `aeon.facade.api`.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PySet, PyTuple};

use crate::builders::{
    new_abstraction_type, new_application, new_conjunction, new_implication, new_liquid_app,
    new_liquid_constraint, new_liquid_horn_application, new_liquid_literal_bool,
    new_liquid_literal_float, new_liquid_literal_int, new_liquid_literal_string, new_liquid_var,
    new_refined_type, new_type_polymorphism, new_uninterpreted_function_declaration, new_var,
};
use crate::kind::{BaseKind, Kind, StarKind};
use crate::liquefy::{instantiate_refinement_in_type, liquefy, substitution_in_type};
use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidVar,
};
use crate::name::Name;
use crate::smt_ctx::mk_liquid_and;
use crate::substitutions::{substitute_vartype, substitution_in_liquid, type_substitution};
use crate::term_subst::{instantiate_refinement_with_horn_in_type, substitution_liquid_in_term, substitution_liquid_in_type};
use crate::terms::{
    Abstraction, Annotation, Application, Hole, If, Let, Literal, Rec, RefinementAbstraction,
    RefinementApplication, Term, TypeAbstraction, TypeApplication, Var,
};
use crate::typectx::TypingContext;
use crate::types::{
    AbstractionType, ExistentialType, RefinedType, RefinementPolymorphism, TypeConstructor,
    TypePolymorphism, TypeVar,
};

// =============================================================================
// Helpers — Python-side imports cached as needed.
// =============================================================================

fn api_error(py: Python<'_>, cls: &str) -> PyResult<PyObject> {
    let api = py.import_bound("aeon.facade.api")?;
    Ok(api.getattr(cls)?.unbind())
}

fn clone_binders(py: Python<'_>, b: &[(Py<Name>, PyObject)]) -> Vec<(Py<Name>, PyObject)> {
    b.iter().map(|(n, t)| (n.clone_ref(py), t.clone_ref(py))).collect()
}

fn raise_api(py: Python<'_>, cls: &str, args: Vec<PyObject>) -> PyErr {
    let result: PyResult<PyErr> = (|| {
        let cls_obj = api_error(py, cls)?;
        let tup = PyTuple::new_bound(py, &args);
        let err_inst = cls_obj.bind(py).call1(tup)?;
        Ok(PyErr::from_value_bound(err_inst))
    })();
    result.unwrap_or_else(|e| e)
}

fn is_op_name(n: &str) -> bool {
    matches!(
        n,
        "==" | "!=" | "<" | "<=" | ">" | ">=" | "-->" | "&&" | "||" | "+" | "-" | "*" | "/"
            | "%" | "!" | "Set_sng" | "Set_cup" | "Set_cap" | "Set_dif" | "Set_mem" | "Set_sub"
    )
}

fn fresh_id(py: Python<'_>) -> PyResult<i64> {
    crate::name::next_fresh_id(py)
}

fn fresh_name(py: Python<'_>, prefix: &str) -> PyResult<Py<Name>> {
    let id = fresh_id(py)?;
    Py::new(py, Name { name: prefix.to_string(), id })
}

fn ctrue(py: Python<'_>) -> PyResult<PyObject> {
    let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
    new_liquid_constraint(py, lb, None)
}

fn t_bool_obj(py: Python<'_>) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: "Bool".to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    crate::builders::new_type_constructor(py, n, empty, crate::loc::default_location(py))
}
fn t_int_obj(py: Python<'_>) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: "Int".to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    crate::builders::new_type_constructor(py, n, empty, crate::loc::default_location(py))
}
fn t_float_obj(py: Python<'_>) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: "Float".to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    crate::builders::new_type_constructor(py, n, empty, crate::loc::default_location(py))
}
fn t_string_obj(py: Python<'_>) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: "String".to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    crate::builders::new_type_constructor(py, n, empty, crate::loc::default_location(py))
}
fn t_set_obj(py: Python<'_>) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: "Set".to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    crate::builders::new_type_constructor(py, n, empty, crate::loc::default_location(py))
}
fn top_obj(py: Python<'_>) -> PyResult<PyObject> {
    let core = py.import_bound("aeon.core.types")?;
    Ok(core.getattr("top")?.unbind())
}

fn is_bare(py: Python<'_>, ty: &PyObject) -> PyResult<bool> {
    let core = py.import_bound("aeon.core.types")?;
    core.getattr("is_bare")?.call1((ty,))?.extract::<bool>()
}

fn type_free_term_vars(py: Python<'_>, ty: &PyObject) -> PyResult<Vec<Py<Name>>> {
    let core = py.import_bound("aeon.core.types")?;
    let result = core.getattr("type_free_term_vars")?.call1((ty,))?;
    let list = result.downcast::<PyList>()?;
    let mut out: Vec<Py<Name>> = Vec::with_capacity(list.len());
    for i in 0..list.len() {
        out.push(list.get_item(i)?.downcast::<Name>()?.clone().unbind());
    }
    Ok(out)
}

fn with_binders(py: Python<'_>, binders: &[(Py<Name>, PyObject)], ty: PyObject) -> PyResult<PyObject> {
    if binders.is_empty() {
        return Ok(ty);
    }
    // Mirror aeon.core.types.with_binders: flatten existing ExistentialType.
    let core = py.import_bound("aeon.core.types")?;
    let tuple_elems: Vec<Py<PyTuple>> = binders
        .iter()
        .map(|(n, t)| {
            let tup =
                PyTuple::new_bound(py, &[n.clone_ref(py).into_any(), t.clone_ref(py)]);
            tup.unbind()
        })
        .collect();
    let outer_tuple = PyTuple::new_bound(py, &tuple_elems);
    Ok(core
        .getattr("with_binders")?
        .call1((outer_tuple, ty))?
        .unbind())
}

fn ensure_refined_rs(py: Python<'_>, ty: PyObject) -> PyResult<PyObject> {
    crate::sub::ensure_refined(py, ty)
}

fn implication_constraint_rs(
    py: Python<'_>,
    name: Py<Name>,
    ty: PyObject,
    c: PyObject,
    loc: Option<PyObject>,
    reflected_impl: Option<PyObject>,
) -> PyResult<PyObject> {
    crate::sub::implication_constraint(py, name, ty, c, loc, reflected_impl)
}

fn sub_rs(
    py: Python<'_>,
    ctx: &Py<TypingContext>,
    t1: PyObject,
    t2: PyObject,
    loc: Option<PyObject>,
) -> PyResult<PyObject> {
    crate::sub::sub(py, ctx.clone_ref(py).into_any(), t1, t2, loc)
}

fn fresh_rs(
    py: Python<'_>,
    ctx: &Py<TypingContext>,
    ty: PyObject,
) -> PyResult<PyObject> {
    crate::horn::fresh(py, ctx.clone_ref(py).into_any(), ty)
}

fn names_equal(py: Python<'_>, a: &Py<Name>, b: &Py<Name>) -> bool {
    let a = a.borrow(py);
    let b = b.borrow(py);
    a.name == b.name && a.id == b.id
}

// =============================================================================
// Primitive types / operators.
// =============================================================================

fn prim_litbool(py: Python<'_>, v: bool) -> PyResult<PyObject> {
    let vname = fresh_name(py, "v")?;
    let tb = t_bool_obj(py)?;
    let ref_expr = if v {
        new_liquid_var(py, vname.clone_ref(py), crate::loc::default_location(py))?
    } else {
        let not_n = Py::new(py, Name { name: "!".to_string(), id: 0 })?;
        let lv = new_liquid_var(py, vname.clone_ref(py), crate::loc::default_location(py))?;
        let args = PyList::new_bound(py, &[lv]).unbind();
        new_liquid_app(py, not_n, args, crate::loc::default_location(py))?
    };
    new_refined_type(py, vname, tb, ref_expr, crate::loc::default_location(py))
}

fn prim_litint(py: Python<'_>, v: i64) -> PyResult<PyObject> {
    let vname = fresh_name(py, "v")?;
    let tb = t_int_obj(py)?;
    let lv = new_liquid_var(py, vname.clone_ref(py), crate::loc::default_location(py))?;
    let lit = new_liquid_literal_int(py, v, crate::loc::default_location(py))?;
    let eq_n = Py::new(py, Name { name: "==".to_string(), id: 0 })?;
    let args = PyList::new_bound(py, &[lv, lit]).unbind();
    let app = new_liquid_app(py, eq_n, args, crate::loc::default_location(py))?;
    new_refined_type(py, vname, tb, app, crate::loc::default_location(py))
}

fn prim_litfloat(py: Python<'_>, v: f64) -> PyResult<PyObject> {
    let vname = fresh_name(py, "v")?;
    let tb = t_float_obj(py)?;
    let lv = new_liquid_var(py, vname.clone_ref(py), crate::loc::default_location(py))?;
    let lit = new_liquid_literal_float(py, v, crate::loc::default_location(py))?;
    let eq_n = Py::new(py, Name { name: "==".to_string(), id: 0 })?;
    let args = PyList::new_bound(py, &[lv, lit]).unbind();
    let app = new_liquid_app(py, eq_n, args, crate::loc::default_location(py))?;
    new_refined_type(py, vname, tb, app, crate::loc::default_location(py))
}

fn prim_litstring(py: Python<'_>, v: &str) -> PyResult<PyObject> {
    let vname = fresh_name(py, "v")?;
    let tb = t_string_obj(py)?;
    let lv = new_liquid_var(py, vname.clone_ref(py), crate::loc::default_location(py))?;
    let lit = new_liquid_literal_string(py, v.to_string(), crate::loc::default_location(py))?;
    let eq_n = Py::new(py, Name { name: "==".to_string(), id: 0 })?;
    let args = PyList::new_bound(py, &[lv, lit]).unbind();
    let app = new_liquid_app(py, eq_n, args, crate::loc::default_location(py))?;
    new_refined_type(py, vname, tb, app, crate::loc::default_location(py))
}

fn make_binary_app_type(
    py: Python<'_>,
    op_name: Py<Name>,
    ity: PyObject,
    oty: PyObject,
) -> PyResult<PyObject> {
    let xname = fresh_name(py, "x")?;
    let yname = fresh_name(py, "y")?;
    let zname = fresh_name(py, "z")?;
    let lvx = new_liquid_var(py, xname.clone_ref(py), crate::loc::default_location(py))?;
    let lvy = new_liquid_var(py, yname.clone_ref(py), crate::loc::default_location(py))?;
    let lvz = new_liquid_var(py, zname.clone_ref(py), crate::loc::default_location(py))?;
    let inner_args = PyList::new_bound(py, &[lvx, lvy]).unbind();
    let inner_app = new_liquid_app(py, op_name, inner_args, crate::loc::default_location(py))?;
    let eq_n = Py::new(py, Name { name: "==".to_string(), id: 0 })?;
    let outer_args = PyList::new_bound(py, &[lvz, inner_app]).unbind();
    let outer_app = new_liquid_app(py, eq_n, outer_args, crate::loc::default_location(py))?;
    let output = new_refined_type(py, zname, oty, outer_app, crate::loc::default_location(py))?;
    let appt2 = new_abstraction_type(py, yname, ity.clone_ref(py), output, crate::loc::default_location(py))?;
    let appt1 = new_abstraction_type(py, xname, ity, appt2, crate::loc::default_location(py))?;
    Ok(appt1)
}

fn type_var(py: Python<'_>, name: Py<Name>) -> PyResult<PyObject> {
    crate::builders::new_type_var(py, name, crate::loc::default_location(py))
}

fn prim_op(py: Python<'_>, op_name: &Py<Name>) -> PyResult<PyObject> {
    let name_str = op_name.borrow(py).name.clone();
    let op = op_name.clone_ref(py);
    match name_str.as_str() {
        "%" => {
            let i = t_int_obj(py)?;
            make_binary_app_type(py, op, i.clone_ref(py), i)
        }
        "+" | "-" | "*" | "/" => {
            let name_a = fresh_name(py, "a")?;
            let tv = type_var(py, name_a.clone_ref(py))?;
            let inner =
                make_binary_app_type(py, op, tv.clone_ref(py), tv)?;
            new_type_polymorphism(
                py,
                name_a,
                Py::new(py, (BaseKind, Kind))?.into_any(),
                inner,
                crate::loc::default_location(py),
            )
        }
        "==" | "!=" | ">" | ">=" | "<" | "<=" => {
            let name_a = fresh_name(py, "a")?;
            let tv = type_var(py, name_a.clone_ref(py))?;
            let tb = t_bool_obj(py)?;
            let inner = make_binary_app_type(py, op, tv, tb)?;
            new_type_polymorphism(
                py,
                name_a,
                Py::new(py, (BaseKind, Kind))?.into_any(),
                inner,
                crate::loc::default_location(py),
            )
        }
        "&&" | "||" => make_binary_app_type(py, op, t_bool_obj(py)?, t_bool_obj(py)?),
        "!" => {
            let n = fresh_name(py, "fresh")?;
            new_abstraction_type(py, n, t_bool_obj(py)?, t_bool_obj(py)?, crate::loc::default_location(py))
        }
        "-->" => make_binary_app_type(py, op, t_bool_obj(py)?, t_bool_obj(py)?),
        "Set_sng" => {
            let n = fresh_name(py, "fresh")?;
            new_abstraction_type(py, n, t_int_obj(py)?, t_set_obj(py)?, crate::loc::default_location(py))
        }
        "Set_cup" | "Set_cap" | "Set_dif" => make_binary_app_type(py, op, t_set_obj(py)?, t_set_obj(py)?),
        "Set_mem" => {
            let xname = fresh_name(py, "x")?;
            let sname = fresh_name(py, "s")?;
            let inner = new_abstraction_type(py, sname, t_set_obj(py)?, t_bool_obj(py)?, crate::loc::default_location(py))?;
            new_abstraction_type(py, xname, t_int_obj(py)?, inner, crate::loc::default_location(py))
        }
        "Set_sub" => make_binary_app_type(py, op, t_set_obj(py)?, t_bool_obj(py)?),
        _ => Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "Unknown selfication of {}",
            name_str
        ))),
    }
}

fn rename_liquid_term(py: Python<'_>, refinement: PyObject, old: &Py<Name>, new: &Py<Name>) -> PyResult<PyObject> {
    let b = refinement.bind(py);
    if let Ok(v) = b.downcast::<LiquidVar>() {
        let v = v.borrow();
        if names_equal(py, &v.name, old) {
            return new_liquid_var(py, new.clone_ref(py), crate::loc::default_location(py));
        }
        return Ok(refinement);
    }
    if b.is_instance_of::<LiquidLiteralBool>()
        || b.is_instance_of::<LiquidLiteralInt>()
        || b.is_instance_of::<LiquidLiteralFloat>()
        || b.is_instance_of::<LiquidLiteralString>()
    {
        return Ok(refinement);
    }
    if let Ok(app) = b.downcast::<LiquidApp>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let args = app.args.clone_ref(py);
        let loc = app.loc.clone_ref(py);
        drop(app);
        let new_args = PyList::empty_bound(py);
        let args_b = args.bind(py);
        for i in 0..args_b.len() {
            let a = args_b.get_item(i)?.unbind();
            new_args.append(rename_liquid_term(py, a, old, new)?)?;
        }
        return new_liquid_app(py, fun, new_args.unbind(), loc);
    }
    if let Ok(horn) = b.downcast::<LiquidHornApplication>() {
        let horn = horn.borrow();
        let name = horn.name.clone_ref(py);
        let argtypes = horn.argtypes.clone_ref(py);
        let loc = horn.loc.clone_ref(py);
        drop(horn);
        let new_argtypes = PyList::empty_bound(py);
        let at_b = argtypes.bind(py);
        for i in 0..at_b.len() {
            let tup = at_b.get_item(i)?;
            let x = tup.get_item(0)?.unbind();
            let t = tup.get_item(1)?.unbind();
            let nx = rename_liquid_term(py, x, old, new)?;
            new_argtypes.append(PyTuple::new_bound(py, &[nx, t]))?;
        }
        let new_name = if names_equal(py, &name, old) { new.clone_ref(py) } else { name };
        return new_liquid_horn_application(py, new_name, new_argtypes.unbind(), loc);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err("rename_liquid_term: unsupported"))
}

fn renamed_refined_type(py: Python<'_>, ty: &Bound<'_, RefinedType>) -> PyResult<PyObject> {
    let ty_b = ty.borrow();
    let old_name = ty_b.name.clone_ref(py);
    let inner = ty_b.type_.clone_ref(py);
    let refinement = ty_b.refinement.clone_ref(py);
    drop(ty_b);
    let old_str = old_name.borrow(py).name.clone();
    let id = fresh_id(py)?;
    let new_name = Py::new(py, Name { name: format!("_inner_{}", old_str), id })?;
    let new_refinement = rename_liquid_term(py, refinement, &old_name, &new_name)?;
    new_refined_type(py, new_name, inner, new_refinement, crate::loc::default_location(py))
}

// =============================================================================
// _reflected_impl_for
// =============================================================================

fn liquid_has_horn(py: Python<'_>, t: &PyObject) -> bool {
    let b = t.bind(py);
    if b.is_instance_of::<LiquidHornApplication>() {
        return true;
    }
    if let Ok(app) = b.downcast::<LiquidApp>() {
        let app = app.borrow();
        let args = app.args.clone_ref(py);
        drop(app);
        let args_b = args.bind(py);
        for i in 0..args_b.len() {
            if let Ok(a) = args_b.get_item(i) {
                let ao = a.unbind();
                if liquid_has_horn(py, &ao) {
                    return true;
                }
            }
        }
    }
    false
}

fn liquid_free_vars_rs(py: Python<'_>, t: &PyObject) -> PyResult<Vec<Py<Name>>> {
    let list = crate::liquid::liquid_free_vars(py, t.clone_ref(py))?;
    let lb = list.bind(py);
    let mut out: Vec<Py<Name>> = Vec::with_capacity(lb.len());
    for i in 0..lb.len() {
        out.push(lb.get_item(i)?.downcast::<Name>()?.clone().unbind());
    }
    Ok(out)
}

fn strip_type_level_wrappers(py: Python<'_>, mut t: PyObject) -> PyObject {
    loop {
        let b = t.bind(py);
        if let Ok(ta) = b.downcast::<TypeAbstraction>() {
            t = ta.borrow().body.clone_ref(py);
            continue;
        }
        if let Ok(ra) = b.downcast::<RefinementAbstraction>() {
            t = ra.borrow().body.clone_ref(py);
            continue;
        }
        if let Ok(an) = b.downcast::<Annotation>() {
            t = an.borrow().expr.clone_ref(py);
            continue;
        }
        return t;
    }
}

#[pyfunction]
#[pyo3(name = "_reflected_impl_for", signature = (name, ty, impl_term, has_termination_metric = false))]
pub fn py_reflected_impl_for(
    py: Python<'_>,
    name: Py<Name>,
    ty: PyObject,
    impl_term: PyObject,
    has_termination_metric: bool,
) -> PyResult<Option<PyObject>> {
    reflected_impl_for(py, &name, &ty, &impl_term, has_termination_metric)
}

fn reflected_impl_for(
    py: Python<'_>,
    name: &Py<Name>,
    ty: &PyObject,
    impl_term: &PyObject,
    has_termination_metric: bool,
) -> PyResult<Option<PyObject>> {
    let ty_b = ty.bind(py);
    if !ty_b.is_instance_of::<AbstractionType>()
        && !ty_b.is_instance_of::<TypePolymorphism>()
        && !ty_b.is_instance_of::<RefinementPolymorphism>()
    {
        return Ok(None);
    }
    if !impl_term.bind(py).is_instance_of::<Term>() {
        return Ok(None);
    }
    let mut current = strip_type_level_wrappers(py, impl_term.clone_ref(py));
    let mut impl_params: Vec<Py<Name>> = Vec::new();
    while let Ok(ab) = current.bind(py).downcast::<Abstraction>() {
        let ab = ab.borrow();
        impl_params.push(ab.var_name.clone_ref(py));
        let body = ab.body.clone_ref(py);
        drop(ab);
        current = body;
    }
    if impl_params.is_empty() {
        return Ok(None);
    }
    let mut ty_params: Vec<Py<Name>> = Vec::new();
    let mut cur_ty = ty.clone_ref(py);
    let mut refinement_params: Vec<Py<Name>> = Vec::new();
    loop {
        let b = cur_ty.bind(py);
        if let Ok(tp) = b.downcast::<TypePolymorphism>() {
            cur_ty = tp.borrow().body.clone_ref(py);
            continue;
        }
        if let Ok(rp) = b.downcast::<RefinementPolymorphism>() {
            let rp = rp.borrow();
            refinement_params.push(rp.name.clone_ref(py));
            let body = rp.body.clone_ref(py);
            drop(rp);
            cur_ty = body;
            continue;
        }
        break;
    }
    while let Ok(at) = cur_ty.bind(py).downcast::<AbstractionType>() {
        let at = at.borrow();
        ty_params.push(at.var_name.clone_ref(py));
        let next = at.type_.clone_ref(py);
        drop(at);
        cur_ty = next;
    }
    if ty_params.len() != impl_params.len() {
        return Ok(None);
    }
    let Some(liq) = liquefy(py, current.clone_ref(py))? else {
        return Ok(None);
    };
    if liquid_has_horn(py, &liq) {
        return Ok(None);
    }
    let mut liq = liq;
    for (src, dst) in impl_params.iter().zip(ty_params.iter()) {
        if !names_equal(py, src, dst) {
            let lv = new_liquid_var(py, dst.clone_ref(py), crate::loc::default_location(py))?;
            liq = substitution_in_liquid(py, liq, lv, src.clone_ref(py))?;
        }
    }
    let fvs = liquid_free_vars_rs(py, &liq)?;
    // Reject if any free name is "native" or "native_import".
    for v in &fvs {
        let nm = v.borrow(py).name.clone();
        if nm == "native" || nm == "native_import" {
            return Ok(None);
        }
    }
    // Allowed: ty_params ∪ {name} ∪ ops
    let mut allowed: Vec<Py<Name>> = ty_params.iter().map(|n| n.clone_ref(py)).collect();
    allowed.push(name.clone_ref(py));
    for v in &fvs {
        let vn = v.borrow(py).name.clone();
        let in_allowed = allowed.iter().any(|n| names_equal(py, n, v));
        if !in_allowed && !is_op_name(&vn) {
            return Ok(None);
        }
    }
    let is_recursive_body = fvs.iter().any(|n| names_equal(py, n, name));
    if is_recursive_body && !has_termination_metric {
        return Ok(None);
    }
    if fvs.iter().any(|v| refinement_params.iter().any(|r| names_equal(py, v, r))) {
        return Ok(None);
    }
    let params_tuple = PyTuple::new_bound(
        py,
        ty_params.iter().map(|n| n.clone_ref(py).into_any()).collect::<Vec<_>>(),
    );
    Ok(Some(
        PyTuple::new_bound(py, &[params_tuple.into_any().unbind(), liq])
            .into_any()
            .unbind(),
    ))
}

#[pyfunction]
#[pyo3(name = "is_compatible")]
pub fn py_is_compatible(py: Python<'_>, a: PyObject, b: PyObject) -> PyResult<bool> {
    is_compatible(py, &a, &b)
}

fn is_compatible(py: Python<'_>, a: &PyObject, b: &PyObject) -> PyResult<bool> {
    if a.bind(py).eq(b.bind(py))? {
        return Ok(true);
    }
    Ok(b.bind(py).downcast::<StarKind>().is_ok())
}

// =============================================================================
// synth / check
// =============================================================================

#[pyfunction]
pub fn synth(py: Python<'_>, ctx: &Bound<'_, TypingContext>, t: PyObject) -> PyResult<Py<PyTuple>> {
    let result = synth_inner(py, ctx, t)?;
    Ok(PyTuple::new_bound(py, &[result.0, result.1]).unbind())
}

fn synth_inner(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    t: PyObject,
) -> PyResult<(PyObject, PyObject)> {
    let b = t.bind(py);

    if let Ok(lit) = b.downcast::<Literal>() {
        let lit = lit.borrow();
        let value = lit.value.clone_ref(py);
        let ty = lit.type_.clone_ref(py);
        drop(lit);
        if let Ok(tc) = ty.bind(py).downcast::<TypeConstructor>() {
            let tc = tc.borrow();
            let n = tc.name.borrow(py);
            let n_str = n.name.clone();
            drop(n);
            drop(tc);
            let prim = match n_str.as_str() {
                "Unit" => prim_litbool(py, true)?,
                "Bool" => prim_litbool(py, value.extract::<bool>(py)?)?,
                "Int" => prim_litint(py, value.extract::<i64>(py)?)?,
                "Float" => prim_litfloat(py, value.extract::<f64>(py)?)?,
                "String" => prim_litstring(py, &value.extract::<String>(py)?)?,
                _ => {
                    return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                        "unhandled literal type {}",
                        n_str
                    )))
                }
            };
            return Ok((ctrue(py)?, prim));
        }
    }

    if let Ok(v) = b.downcast::<Var>() {
        let v = v.borrow();
        let name = v.name.clone_ref(py);
        drop(v);
        let nm_str = name.borrow(py).name.clone();
        if is_op_name(&nm_str) {
            return Ok((ctrue(py)?, prim_op(py, &name)?));
        }
        let ctx_py: Py<TypingContext> = ctx.clone().unbind();
        let ty = ctx_py.borrow(py).type_of(py, name.clone_ref(py))?;
        if ty.bind(py).is_none() {
            return Err(raise_api(
                py,
                "CoreVariableNotInContext",
                vec![ctx.clone().into_any().unbind(), t.clone_ref(py)],
            ));
        }
        // Self-ification for refinable types.
        let mut ty = ty;
        let tb = ty.bind(py);
        if tb.is_instance_of::<TypeConstructor>()
            || tb.is_instance_of::<RefinedType>()
            || tb.is_instance_of::<TypeVar>()
        {
            ty = ensure_refined_rs(py, ty)?;
            // After ensure_refined, ty must be a RefinedType.
            let rt = ty.bind(py).downcast::<RefinedType>()?.clone();
            let rt_b = rt.borrow();
            let rt_name = rt_b.name.clone_ref(py);
            drop(rt_b);
            // Avoid name capture
            if names_equal(py, &rt_name, &name) {
                ty = renamed_refined_type(py, &rt)?;
            }
            let rt = ty.bind(py).downcast::<RefinedType>()?.clone();
            let rt_b = rt.borrow();
            let rt_name = rt_b.name.clone_ref(py);
            let rt_inner = rt_b.type_.clone_ref(py);
            let rt_ref = rt_b.refinement.clone_ref(py);
            drop(rt_b);
            // Build (refinement) && (rt.name == t.name)
            let lv_rt = new_liquid_var(py, rt_name.clone_ref(py), crate::loc::default_location(py))?;
            let lv_t = new_liquid_var(py, name.clone_ref(py), crate::loc::default_location(py))?;
            let eq_n = Py::new(py, Name { name: "==".to_string(), id: 0 })?;
            let eq_args = PyList::new_bound(py, &[lv_rt, lv_t]).unbind();
            let eq_app = new_liquid_app(py, eq_n, eq_args, crate::loc::default_location(py))?;
            let and_n = Py::new(py, Name { name: "&&".to_string(), id: 0 })?;
            let and_args = PyList::new_bound(py, &[rt_ref, eq_app]).unbind();
            let and_app = new_liquid_app(py, and_n, and_args, crate::loc::default_location(py))?;
            ty = new_refined_type(py, rt_name, rt_inner, and_app, crate::loc::default_location(py))?;
        }
        return Ok((ctrue(py)?, ty));
    }

    if let Ok(app) = b.downcast::<Application>() {
        let app_b = app.borrow();
        let fun = app_b.fun.clone_ref(py);
        let arg = app_b.arg.clone_ref(py);
        let loc = app_b.loc.clone_ref(py);
        drop(app_b);
        let (c, mut ty) = synth_inner(py, ctx, fun)?;
        // Lift existential binders.
        let mut fun_binders: Vec<(Py<Name>, PyObject)> = Vec::new();
        if let Ok(et) = ty.bind(py).downcast::<ExistentialType>() {
            let et = et.borrow();
            let binders = et.binders.clone_ref(py);
            let body = et.body.clone_ref(py);
            drop(et);
            let bb = binders.bind(py);
            for i in 0..bb.len() {
                let tup = bb.get_item(i)?;
                let bn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
                let bt: PyObject = tup.get_item(1)?.unbind();
                fun_binders.push((bn, bt));
            }
            ty = body;
        }
        let mut ctx_inner: Py<TypingContext> = ctx.clone().unbind();
        for (bn, bt) in &fun_binders {
            let new_ctx = ctx_inner.borrow(py).with_var(py, bn.clone_ref(py), bt.clone_ref(py))?;
            ctx_inner = Py::new(py, new_ctx)?;
        }
        let mut outer_binders = clone_binders(py, &fun_binders);
        if let Ok(at) = ty.bind(py).downcast::<AbstractionType>() {
            let at_b = at.borrow();
            let aname = at_b.var_name.clone_ref(py);
            let atype = at_b.var_type.clone_ref(py);
            let rtype = at_b.type_.clone_ref(py);
            drop(at_b);
            let cp = check_inner(py, ctx_inner.bind(py), arg.clone_ref(py), atype.clone_ref(py))?;
            let t_subs: PyObject;
            let arg_b = arg.bind(py);
            if arg_b.is_instance_of::<Var>() || arg_b.is_instance_of::<Literal>() || arg_b.is_instance_of::<Abstraction>() {
                t_subs = substitution_in_type(py, rtype, arg.clone_ref(py), aname)?;
            } else {
                // existential binder introduction
                let (_, ty_arg) = synth_inner(py, ctx_inner.bind(py), arg.clone_ref(py))?;
                let mut ty_arg = ty_arg;
                if let Ok(et) = ty_arg.bind(py).downcast::<ExistentialType>() {
                    let et = et.borrow();
                    let bs = et.binders.clone_ref(py);
                    let body = et.body.clone_ref(py);
                    drop(et);
                    let bb = bs.bind(py);
                    for i in 0..bb.len() {
                        let tup = bb.get_item(i)?;
                        let bn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
                        let bt: PyObject = tup.get_item(1)?.unbind();
                        outer_binders.push((bn, bt));
                    }
                    ty_arg = body;
                }
                let y_id = fresh_id(py)?;
                let y = Py::new(py, Name { name: "_y".to_string(), id: y_id })?;
                let mut binder_ty = ensure_refined_rs(py, ty_arg)?;
                if let Ok(rt) = binder_ty.bind(py).downcast::<RefinedType>() {
                    let rt = rt.borrow();
                    let rt_name = rt.name.clone_ref(py);
                    let rt_inner = rt.type_.clone_ref(py);
                    let rt_ref = rt.refinement.clone_ref(py);
                    drop(rt);
                    let lv = new_liquid_var(py, y.clone_ref(py), crate::loc::default_location(py))?;
                    let renamed = substitution_in_liquid(py, rt_ref, lv, rt_name)?;
                    binder_ty = new_refined_type(py, y.clone_ref(py), rt_inner, renamed, crate::loc::default_location(py))?;
                }
                outer_binders.push((y.clone_ref(py), binder_ty));
                let var_y = new_var(py, y.clone_ref(py), crate::loc::default_location(py))?;
                t_subs = substitution_in_type(py, rtype, var_y, aname)?;
            }
            let mut c0 = new_conjunction(py, c, cp, None)?;
            for (bn, bt) in fun_binders.iter().rev() {
                c0 = implication_constraint_rs(py, bn.clone_ref(py), bt.clone_ref(py), c0, Some(loc.clone_ref(py)), None)?;
            }
            let _ = loc;
            return Ok((c0, with_binders(py, &outer_binders, t_subs)?));
        }
        return Err(raise_api(
            py,
            "CoreInvalidApplicationError",
            vec![t.clone_ref(py), ty],
        ));
    }

    if let Ok(le) = b.downcast::<Let>() {
        let le_b = le.borrow();
        let var_name = le_b.var_name.clone_ref(py);
        let var_value = le_b.var_value.clone_ref(py);
        let body = le_b.body.clone_ref(py);
        let body_loc = body.bind(py).getattr("loc")?.unbind();
        drop(le_b);
        let (c1, mut t1) = synth_inner(py, ctx, var_value.clone_ref(py))?;
        let mut opened_binders: Vec<(Py<Name>, PyObject)> = Vec::new();
        if let Ok(et) = t1.bind(py).downcast::<ExistentialType>() {
            let et = et.borrow();
            let bs = et.binders.clone_ref(py);
            let body_ty = et.body.clone_ref(py);
            drop(et);
            let bb = bs.bind(py);
            for i in 0..bb.len() {
                let tup = bb.get_item(i)?;
                let bn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
                let bt: PyObject = tup.get_item(1)?.unbind();
                opened_binders.push((bn, bt));
            }
            t1 = body_ty;
        }
        let mut nctx: Py<TypingContext> = ctx.clone().unbind();
        for (bn, bt) in &opened_binders {
            let new_ctx = nctx.borrow(py).with_var(py, bn.clone_ref(py), bt.clone_ref(py))?;
            nctx = Py::new(py, new_ctx)?;
        }
        let nctx2 = nctx.borrow(py).with_var(py, var_name.clone_ref(py), t1.clone_ref(py))?;
        nctx = Py::new(py, nctx2)?;
        let (c2, mut t2) = synth_inner(py, nctx.bind(py), body)?;
        let reflected_impl = reflected_impl_for(py, &var_name, &t1, &var_value, false)?;
        let mut inner = implication_constraint_rs(
            py,
            var_name.clone_ref(py),
            t1.clone_ref(py),
            c2,
            Some(body_loc.clone_ref(py)),
            reflected_impl,
        )?;
        for (bn, bt) in opened_binders.iter().rev() {
            inner = implication_constraint_rs(py, bn.clone_ref(py), bt.clone_ref(py), inner, Some(body_loc.clone_ref(py)), None)?;
        }
        // Detect leaking binders.
        let t2_free = type_free_term_vars(py, &t2)?;
        let mut leaking: Vec<(Py<Name>, PyObject)> = Vec::new();
        for (bn, bt) in &opened_binders {
            if t2_free.iter().any(|n| names_equal(py, n, bn)) {
                leaking.push((bn.clone_ref(py), bt.clone_ref(py)));
            }
        }
        if t2_free.iter().any(|n| names_equal(py, n, &var_name)) {
            leaking.push((var_name.clone_ref(py), t1.clone_ref(py)));
        }
        if !leaking.is_empty() {
            t2 = with_binders(py, &leaking, t2)?;
        }
        return Ok((new_conjunction(py, c1, inner, None)?, t2));
    }

    if let Ok(rc) = b.downcast::<Rec>() {
        let rc_b = rc.borrow();
        let var_name = rc_b.var_name.clone_ref(py);
        let var_type = rc_b.var_type.clone_ref(py);
        let var_value = rc_b.var_value.clone_ref(py);
        let body = rc_b.body.clone_ref(py);
        let decreasing_by = rc_b.decreasing_by.clone_ref(py);
        let var_value_loc = var_value.bind(py).getattr("loc")?.unbind();
        let body_loc = body.bind(py).getattr("loc")?.unbind();
        drop(rc_b);
        let nrctx_inner = ctx.borrow().with_var(py, var_name.clone_ref(py), var_type.clone_ref(py))?;
        let nrctx = Py::new(py, nrctx_inner)?;
        let c1 = check_inner(py, nrctx.bind(py), var_value.clone_ref(py), var_type.clone_ref(py))?;
        let (c2, mut t2) = synth_inner(py, nrctx.bind(py), body)?;
        let has_metric = decreasing_by.bind(py).len() > 0;
        let reflected_impl = reflected_impl_for(py, &var_name, &var_type, &var_value, has_metric)?;
        let c1 = implication_constraint_rs(
            py,
            var_name.clone_ref(py),
            var_type.clone_ref(py),
            c1,
            Some(var_value_loc.clone_ref(py)),
            reflected_impl.as_ref().map(|x| x.clone_ref(py)),
        )?;
        let c2 = implication_constraint_rs(
            py,
            var_name.clone_ref(py),
            var_type.clone_ref(py),
            c2,
            Some(body_loc.clone_ref(py)),
            reflected_impl.as_ref().map(|x| x.clone_ref(py)),
        )?;
        let term_c = crate::termination::termination_metric_constraints(
            py,
            t.bind(py).downcast::<Rec>()?,
            Some(nrctx.clone_ref(py).into_any()),
        )?;
        let term_c = implication_constraint_rs(
            py,
            var_name.clone_ref(py),
            var_type.clone_ref(py),
            term_c,
            Some(var_value_loc),
            reflected_impl,
        )?;
        let t2_free = type_free_term_vars(py, &t2)?;
        if t2_free.iter().any(|n| names_equal(py, n, &var_name)) {
            t2 = with_binders(py, &[(var_name.clone_ref(py), var_type.clone_ref(py))], t2)?;
        }
        let inner = new_conjunction(py, c1, c2, None)?;
        let combined = new_conjunction(py, inner, term_c, None)?;
        return Ok((combined, t2));
    }

    if let Ok(an) = b.downcast::<Annotation>() {
        let an_b = an.borrow();
        let expr = an_b.expr.clone_ref(py);
        let ty = an_b.type_.clone_ref(py);
        drop(an_b);
        let ctx_py: Py<TypingContext> = ctx.clone().unbind();
        let nty = fresh_rs(py, &ctx_py, ty)?;
        let c = check_inner(py, ctx, expr, nty.clone_ref(py))?;
        return Ok((c, nty));
    }

    if let Ok(tap) = b.downcast::<TypeApplication>() {
        let tap_b = tap.borrow();
        let body = tap_b.body.clone_ref(py);
        let ty = tap_b.type_.clone_ref(py);
        drop(tap_b);
        if !is_bare(py, &ty)? {
            return Err(raise_api(
                py,
                "CoreTypeApplicationRequiresBareTypesError",
                vec![t.clone_ref(py), ty],
            ));
        }
        let (c, tabs) = synth_inner(py, ctx, body)?;
        let ctx_py: Py<TypingContext> = ctx.clone().unbind();
        let mut nty = fresh_rs(py, &ctx_py, ty)?;
        let mut k = ctx_py.borrow(py).kind_of(py, nty.clone_ref(py))?;
        if let Ok(rt) = nty.bind(py).downcast::<RefinedType>() {
            let rt = rt.borrow();
            let refinement = rt.refinement.bind(py);
            if refinement.is_instance_of::<LiquidHornApplication>() {
                let inner_ty = rt.type_.clone_ref(py);
                drop(rt);
                nty = inner_ty;
                k = ctx_py.borrow(py).kind_of(py, nty.clone_ref(py))?;
            }
        }
        if let Ok(tp) = tabs.bind(py).downcast::<TypePolymorphism>() {
            let tp_b = tp.borrow();
            let tp_body = tp_b.body.clone_ref(py);
            let tp_name = tp_b.name.clone_ref(py);
            let tp_kind = tp_b.kind.clone_ref(py);
            drop(tp_b);
            let s = type_substitution(py, tp_body, tp_name, nty.clone_ref(py))?;
            if k.bind(py).is_none() || !is_compatible(py, &k, &tp_kind)? {
                return Err(raise_api(
                    py,
                    "CoreWrongKindInTypeApplicationError",
                    vec![t.clone_ref(py), nty, tp_kind, k],
                ));
            }
            return Ok((c, s));
        }
        if !tabs.bind(py).is_instance_of::<AbstractionType>() {
            return Err(raise_api(
                py,
                "CoreInvalidApplicationError",
                vec![t.clone_ref(py), tabs],
            ));
        }
        return Ok((c, tabs));
    }

    if let Ok(rap) = b.downcast::<RefinementApplication>() {
        let rap_b = rap.borrow();
        let body = rap_b.body.clone_ref(py);
        let refinement = rap_b.refinement.clone_ref(py);
        drop(rap_b);
        let (c, rp) = synth_inner(py, ctx, body)?;
        if !rp.bind(py).is_instance_of::<RefinementPolymorphism>() {
            return Err(raise_api(
                py,
                "CoreInvalidApplicationError",
                vec![t.clone_ref(py), rp],
            ));
        }
        if refinement.bind(py).is_instance_of::<Hole>() {
            let horn_name = fresh_name(py, "kappa")?;
            let rpb = rp.bind(py).downcast::<RefinementPolymorphism>()?.clone();
            let rpb_b = rpb.borrow();
            let rp_body = rpb_b.body.clone_ref(py);
            let rp_name = rpb_b.name.clone_ref(py);
            let rp_sort = rpb_b.sort.clone_ref(py);
            drop(rpb_b);
            let nty = instantiate_refinement_with_horn_in_type(py, rp_body, rp_name, rp_sort, horn_name)?;
            return Ok((c, nty));
        }
        assert!(refinement.bind(py).is_instance_of::<Abstraction>());
        let rpb = rp.bind(py).downcast::<RefinementPolymorphism>()?.clone();
        let rpb_b = rpb.borrow();
        let rp_body = rpb_b.body.clone_ref(py);
        let rp_name = rpb_b.name.clone_ref(py);
        let rp_sort = rpb_b.sort.clone_ref(py);
        drop(rpb_b);
        let und = fresh_name(py, "_")?;
        let pred_ty = new_abstraction_type(py, und, rp_sort, t_bool_obj(py)?, crate::loc::default_location(py))?;
        let c_ref = check_inner(py, ctx, refinement.clone_ref(py), pred_ty)?;
        let nty = instantiate_refinement_in_type(py, rp_body, rp_name, refinement)?;
        return Ok((new_conjunction(py, c, c_ref, None)?, nty));
    }

    if let Ok(hole) = b.downcast::<Hole>() {
        let hole_b = hole.borrow();
        let hn = hole_b.name.clone_ref(py);
        drop(hole_b);
        let nm_str = hn.borrow(py).name.clone();
        let id = fresh_id(py)?;
        let name_a = Py::new(py, Name { name: nm_str, id })?;
        let tv = type_var(py, name_a.clone_ref(py))?;
        let tp = new_type_polymorphism(
            py,
            name_a,
            Py::new(py, (StarKind, Kind))?.into_any(),
            tv,
            crate::loc::default_location(py),
        )?;
        return Ok((ctrue(py)?, tp));
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unhandled term {} in synth",
        b.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn check(py: Python<'_>, ctx: &Bound<'_, TypingContext>, t: PyObject, ty: PyObject) -> PyResult<PyObject> {
    check_inner(py, ctx, t, ty)
}

fn check_inner(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    t: PyObject,
    ty: PyObject,
) -> PyResult<PyObject> {
    let ctx_py: Py<TypingContext> = ctx.clone().unbind();
    let sk = Py::new(py, (StarKind, Kind))?.into_any();
    if !crate::well_formed::wellformed(py, &ctx_py, &ty, &sk)? {
        return Err(raise_api(py, "CoreWellformnessError", vec![ty.clone_ref(py)]));
    }
    let tb = t.bind(py);
    let ty_b = ty.bind(py);

    // case (Abstraction(name, body), AbstractionType(var_name, var_type, ret))
    if let (Ok(ab), Ok(at)) = (tb.downcast::<Abstraction>(), ty_b.downcast::<AbstractionType>()) {
        let ab = ab.borrow();
        let name = ab.var_name.clone_ref(py);
        let body = ab.body.clone_ref(py);
        let body_loc = body.bind(py).getattr("loc")?.unbind();
        drop(ab);
        let at = at.borrow();
        let var_name = at.var_name.clone_ref(py);
        let var_type = at.var_type.clone_ref(py);
        let ret = at.type_.clone_ref(py);
        drop(at);
        let var_t = new_var(py, name.clone_ref(py), crate::loc::default_location(py))?;
        let ret = substitution_in_type(py, ret, var_t, var_name)?;
        let new_ctx_inner = ctx.borrow().with_var(py, name.clone_ref(py), var_type.clone_ref(py))?;
        let new_ctx = Py::new(py, new_ctx_inner)?;
        let c = check_inner(py, new_ctx.bind(py), body, ret)?;
        return implication_constraint_rs(py, name, var_type, c, Some(body_loc), None);
    }

    // case (Let(name, val, body), _)
    if let Ok(le) = tb.downcast::<Let>() {
        let le_b = le.borrow();
        let name = le_b.var_name.clone_ref(py);
        let val = le_b.var_value.clone_ref(py);
        let body = le_b.body.clone_ref(py);
        let body_loc = body.bind(py).getattr("loc")?.unbind();
        drop(le_b);
        let (c1, mut t1) = synth_inner(py, ctx, val.clone_ref(py))?;
        let mut opened_binders: Vec<(Py<Name>, PyObject)> = Vec::new();
        if let Ok(et) = t1.bind(py).downcast::<ExistentialType>() {
            let et = et.borrow();
            let bs = et.binders.clone_ref(py);
            let body_ty = et.body.clone_ref(py);
            drop(et);
            let bb = bs.bind(py);
            for i in 0..bb.len() {
                let tup = bb.get_item(i)?;
                let bn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
                let bt: PyObject = tup.get_item(1)?.unbind();
                opened_binders.push((bn, bt));
            }
            t1 = body_ty;
        }
        let mut nctx: Py<TypingContext> = ctx.clone().unbind();
        for (bn, bt) in &opened_binders {
            let new_ctx = nctx.borrow(py).with_var(py, bn.clone_ref(py), bt.clone_ref(py))?;
            nctx = Py::new(py, new_ctx)?;
        }
        let nctx2 = nctx.borrow(py).with_var(py, name.clone_ref(py), t1.clone_ref(py))?;
        nctx = Py::new(py, nctx2)?;
        let c2 = check_inner(py, nctx.bind(py), body, ty.clone_ref(py))?;
        let reflected_impl = reflected_impl_for(py, &name, &t1, &val, false)?;
        let mut inner = implication_constraint_rs(py, name, t1, c2, Some(body_loc.clone_ref(py)), reflected_impl)?;
        for (bn, bt) in opened_binders.iter().rev() {
            inner = implication_constraint_rs(py, bn.clone_ref(py), bt.clone_ref(py), inner, Some(body_loc.clone_ref(py)), None)?;
        }
        return new_conjunction(py, c1, inner, None);
    }

    // case (Rec(var_name, var_type, var_value, body), _)
    if let Ok(rc) = tb.downcast::<Rec>() {
        let rc_b = rc.borrow();
        let var_name = rc_b.var_name.clone_ref(py);
        let var_type = rc_b.var_type.clone_ref(py);
        let var_value = rc_b.var_value.clone_ref(py);
        let body = rc_b.body.clone_ref(py);
        let decreasing_by = rc_b.decreasing_by.clone_ref(py);
        let var_value_loc = var_value.bind(py).getattr("loc")?.unbind();
        let body_loc = body.bind(py).getattr("loc")?.unbind();
        drop(rc_b);
        let t1 = fresh_rs(py, &ctx_py, var_type.clone_ref(py))?;
        let nrctx_inner = ctx.borrow().with_var(py, var_name.clone_ref(py), t1.clone_ref(py))?;
        let nrctx = Py::new(py, nrctx_inner)?;
        let c1 = check_inner(py, nrctx.bind(py), var_value.clone_ref(py), var_type.clone_ref(py))?;
        let c2 = check_inner(py, nrctx.bind(py), body, ty.clone_ref(py))?;
        let has_metric = decreasing_by.bind(py).len() > 0;
        let reflected_impl = reflected_impl_for(py, &var_name, &t1, &var_value, has_metric)?;
        let c1 = implication_constraint_rs(py, var_name.clone_ref(py), t1.clone_ref(py), c1, Some(var_value_loc.clone_ref(py)), reflected_impl.as_ref().map(|x| x.clone_ref(py)))?;
        let c2 = implication_constraint_rs(py, var_name.clone_ref(py), t1.clone_ref(py), c2, Some(body_loc.clone_ref(py)), reflected_impl.as_ref().map(|x| x.clone_ref(py)))?;
        let term_c = crate::termination::termination_metric_constraints(
            py,
            t.bind(py).downcast::<Rec>()?,
            Some(nrctx.clone_ref(py).into_any()),
        )?;
        let term_c = implication_constraint_rs(py, var_name.clone_ref(py), t1.clone_ref(py), term_c, Some(var_value_loc), reflected_impl)?;
        let inner = new_conjunction(py, c1, c2, None)?;
        return new_conjunction(py, inner, term_c, None);
    }

    // case (If(cond, then, otherwise), _)
    if let Ok(ife) = tb.downcast::<If>() {
        let ife_b = ife.borrow();
        let cond = ife_b.cond.clone_ref(py);
        let then = ife_b.then.clone_ref(py);
        let otherwise = ife_b.otherwise.clone_ref(py);
        let then_loc = then.bind(py).getattr("loc")?.unbind();
        let otherwise_loc = otherwise.bind(py).getattr("loc")?.unbind();
        drop(ife_b);
        let y_id = fresh_id(py)?;
        let y = Py::new(py, Name { name: "_cond".to_string(), id: y_id })?;
        let Some(liq_cond) = liquefy(py, cond.clone_ref(py))? else {
            return Err(pyo3::exceptions::PyAssertionError::new_err("If condition cannot be liquefied"));
        };
        let tb_obj = t_bool_obj(py)?;
        if !check_type_inner(py, ctx, cond.clone_ref(py), tb_obj.clone_ref(py))? {
            return Err(raise_api(py, "CoreTypingRelation", vec![ctx.clone().into_any().unbind(), cond.clone_ref(py), tb_obj.clone_ref(py)]));
        }
        let c0 = check_inner(py, ctx, cond, tb_obj)?;
        let name_pos = fresh_name(py, "branch_pos")?;
        let pos_rt = new_refined_type(py, name_pos, t_int_obj(py)?, liq_cond.clone_ref(py), crate::loc::default_location(py))?;
        let then_c = check_inner(py, ctx, then, ty.clone_ref(py))?;
        let c1 = implication_constraint_rs(py, y.clone_ref(py), pos_rt, then_c, Some(then_loc), None)?;
        let name_neg = fresh_name(py, "branch_neg")?;
        let not_n = Py::new(py, Name { name: "!".to_string(), id: 0 })?;
        let neg_args = PyList::new_bound(py, &[liq_cond]).unbind();
        let neg_app = new_liquid_app(py, not_n, neg_args, crate::loc::default_location(py))?;
        let neg_rt = new_refined_type(py, name_neg, t_int_obj(py)?, neg_app, crate::loc::default_location(py))?;
        let otherwise_c = check_inner(py, ctx, otherwise, ty)?;
        let c2 = implication_constraint_rs(py, y, neg_rt, otherwise_c, Some(otherwise_loc), None)?;
        let inner = new_conjunction(py, c1, c2, None)?;
        return new_conjunction(py, c0, inner, None);
    }

    // case (TypeAbstraction(name, kind, body), TypePolymorphism(var_name, var_kind, var_body))
    if let (Ok(ta), Ok(tp)) = (tb.downcast::<TypeAbstraction>(), ty_b.downcast::<TypePolymorphism>()) {
        let ta = ta.borrow();
        let name = ta.name.clone_ref(py);
        let kind = ta.kind.clone_ref(py);
        let body = ta.body.clone_ref(py);
        drop(ta);
        let tp = tp.borrow();
        let var_name = tp.name.clone_ref(py);
        let var_kind = tp.kind.clone_ref(py);
        let var_body = tp.body.clone_ref(py);
        drop(tp);
        let is_base = var_kind.bind(py).downcast::<BaseKind>().is_ok();
        if is_base && !kind.bind(py).eq(var_kind.bind(py))? {
            return Err(raise_api(
                py,
                "CoreWrongKindInTypeApplicationError",
                vec![t.clone_ref(py), ty.clone_ref(py), var_kind.clone_ref(py), var_kind],
            ));
        }
        let tv = type_var(py, name.clone_ref(py))?;
        let itype = substitute_vartype(py, var_body, tv, var_name)?;
        let new_ctx_inner = ctx.borrow().with_typevar(py, name, var_kind)?;
        let new_ctx = Py::new(py, new_ctx_inner)?;
        return check_inner(py, new_ctx.bind(py), body, itype);
    }

    // case (RefinementAbstraction(pname, psort, inner), RefinementPolymorphism(rname, rsort, rbody))
    if let (Ok(ra), Ok(rp)) = (tb.downcast::<RefinementAbstraction>(), ty_b.downcast::<RefinementPolymorphism>()) {
        let ra = ra.borrow();
        let pname = ra.name.clone_ref(py);
        let psort = ra.sort.clone_ref(py);
        let inner = ra.body.clone_ref(py);
        let t_loc = t.bind(py).getattr("loc")?.unbind();
        drop(ra);
        let rp = rp.borrow();
        let rname = rp.name.clone_ref(py);
        let rsort = rp.sort.clone_ref(py);
        let rbody = rp.body.clone_ref(py);
        drop(rp);
        let c_sort = sub_rs(py, &ctx_py, psort.clone_ref(py), rsort.clone_ref(py), Some(t_loc))?;
        let und = fresh_name(py, "_")?;
        let fk_type = new_abstraction_type(py, und, rsort.clone_ref(py), t_bool_obj(py)?, crate::loc::default_location(py))?;
        let ctx_ext_inner = ctx.borrow().with_var(py, pname.clone_ref(py), fk_type.clone_ref(py))?;
        let ctx_ext = Py::new(py, ctx_ext_inner)?;
        let lv_p = new_liquid_var(py, pname.clone_ref(py), crate::loc::default_location(py))?;
        let body_open = substitution_liquid_in_type(py, rbody, lv_p.clone_ref(py), rname.clone_ref(py))?;
        let inner_sub = substitution_liquid_in_term(py, inner, lv_p, rname)?;
        let c_body = check_inner(py, ctx_ext.bind(py), inner_sub, body_open)?;
        let ufd = new_uninterpreted_function_declaration(py, pname, fk_type, c_body)?;
        return new_conjunction(py, c_sort, ufd, None);
    }

    // case (_, RefinementPolymorphism(name, sort, body))
    if let Ok(rp) = ty_b.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let name = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        drop(rp);
        let name_str = name.borrow(py).name.clone();
        let fk_id = fresh_id(py)?;
        let fk_name = Py::new(py, Name { name: format!("_f{}", name_str), id: fk_id })?;
        let und = fresh_name(py, "_")?;
        let fk_type = new_abstraction_type(py, und, sort.clone_ref(py), t_bool_obj(py)?, crate::loc::default_location(py))?;
        let ctx_ext_inner = ctx.borrow().with_var(py, fk_name.clone_ref(py), fk_type.clone_ref(py))?;
        let ctx_ext = Py::new(py, ctx_ext_inner)?;
        let lv_fk = new_liquid_var(py, fk_name.clone_ref(py), crate::loc::default_location(py))?;
        let body_sub = substitution_liquid_in_type(py, body, lv_fk.clone_ref(py), name.clone_ref(py))?;
        let term_sub = substitution_liquid_in_term(py, t.clone_ref(py), lv_fk, name)?;
        let c = check_inner(py, ctx_ext.bind(py), term_sub, body_sub)?;
        return new_uninterpreted_function_declaration(py, fk_name, fk_type, c);
    }

    // Default: synth, then sub.
    let t_loc = t.bind(py).getattr("loc")?.unbind();
    let (c, s) = synth_inner(py, ctx, t.clone_ref(py))?;
    let cp = sub_rs(py, &ctx_py, s.clone_ref(py), ty.clone_ref(py), Some(t_loc))?;
    // Detect ctrue == LiquidConstraint(LiquidLiteralBool(False)) — Python uses
    // a literal equality check; we mirror it by inspecting the structure.
    if let Ok(lc) = cp.bind(py).downcast::<crate::vcs::LiquidConstraint>() {
        let lc = lc.borrow();
        if let Ok(lb) = lc.expr.bind(py).downcast::<LiquidLiteralBool>() {
            if !lb.borrow().value {
                return Err(raise_api(
                    py,
                    "CoreSubtypingError",
                    vec![ctx.clone().into_any().unbind(), t.clone_ref(py), s, ty],
                ));
            }
        }
    }
    new_conjunction(py, c, cp, None)
}

#[pyfunction]
#[pyo3(signature = (ctx, t, ty = None))]
pub fn check_type(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    t: PyObject,
    ty: Option<PyObject>,
) -> PyResult<bool> {
    let ty = match ty {
        Some(ty) => ty,
        None => top_obj(py)?,
    };
    check_type_inner(py, ctx, t, ty)
}

fn check_type_inner(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    t: PyObject,
    ty: PyObject,
) -> PyResult<bool> {
    let ctx_py: Py<TypingContext> = ctx.clone().unbind();
    let sk = Py::new(py, (StarKind, Kind))?.into_any();
    if !crate::well_formed::wellformed(py, &ctx_py, &ty, &sk)? {
        return Ok(false);
    }
    match check_inner(py, ctx, t, ty) {
        Ok(constraint) => crate::entailment::entailment(py, ctx, constraint),
        Err(e) => {
            // CoreTypeCheckingError → return False, anything else → propagate.
            let core_err_cls = py
                .import_bound("aeon.facade.api")?
                .getattr("CoreTypeCheckingError")?;
            let val = e.value_bound(py);
            if val.is_instance(&core_err_cls)? {
                Ok(false)
            } else {
                Err(e)
            }
        }
    }
}

// =============================================================================
// constraint_to_parts / check_type_errors
// =============================================================================

#[pyfunction]
#[pyo3(signature = (c, typing_ctx = None))]
pub fn constraint_to_parts(
    py: Python<'_>,
    c: PyObject,
    typing_ctx: Option<PyObject>,
) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    let atoms = match typing_ctx.as_ref() {
        Some(t) => {
            let bound = t.bind(py).downcast::<TypingContext>()?.clone();
            crate::qualifiers::extract_qualifier_atoms(py, &bound, None, None, 512)?
                .into_any()
        }
        None => pyo3::types::PyFrozenSet::empty_bound(py)?.into_any().unbind(),
    };

    let cnf = crate::helpers::conjunctive_normal_form(py, c)?;
    let cnf_b = cnf.bind(py);
    for i in 0..cnf_b.len() {
        let cons = cnf_b.get_item(i)?.unbind();
        if crate::helpers::is_implication_true(py, cons.clone_ref(py))? {
            continue;
        }
        let ok = crate::horn::solve(
            py,
            cons.clone_ref(py),
            typing_ctx.as_ref().map(|t| t.clone_ref(py)),
            Some(atoms.clone_ref(py)),
        )?;
        if ok {
            continue;
        }
        let vcs = crate::helpers::split_or_in_conclusion(py, cons)?;
        let vcs_b = vcs.bind(py);
        for j in 0..vcs_b.len() {
            let vc = vcs_b.get_item(j)?.unbind();
            let ok2 = crate::horn::solve(
                py,
                vc.clone_ref(py),
                typing_ctx.as_ref().map(|t| t.clone_ref(py)),
                Some(atoms.clone_ref(py)),
            )?;
            if !ok2 {
                let cons_simp = crate::helpers::simplify_constraint(py, vc)?;
                let empty_set = PySet::empty_bound(py)?.unbind();
                let tup = crate::helpers::remove_unrelated_context(py, cons_simp, empty_set)?;
                let cleaned = tup.bind(py).get_item(0)?.unbind();
                let loc = crate::helpers::constraint_location(py, cleaned.clone_ref(py))?;
                let pair = PyTuple::new_bound(py, &[cleaned, loc]);
                out.append(pair)?;
                break;
            }
        }
    }
    Ok(out.unbind())
}

#[pyfunction]
pub fn check_type_errors(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    term: PyObject,
    expected_type: PyObject,
) -> PyResult<Py<PyList>> {
    let ctx_py: Py<TypingContext> = ctx.clone().unbind();
    let sk = Py::new(py, (StarKind, Kind))?.into_any();
    let out = PyList::empty_bound(py);

    if !crate::well_formed::wellformed(py, &ctx_py, &expected_type, &sk)? {
        let err_cls = api_error(py, "CoreWellformnessError")?;
        let err = err_cls.bind(py).call1((expected_type,))?.unbind();
        out.append(err)?;
        return Ok(out.unbind());
    }

    let type_errors_result = (|| -> PyResult<Vec<PyObject>> {
        let constraint = check_inner(py, ctx, term.clone_ref(py), expected_type.clone_ref(py))?;
        let v = crate::entailment::entailment(py, ctx, constraint.clone_ref(py))?;
        if v {
            return Ok(Vec::new());
        }
        let full_constraint = crate::entailment::entailment_context(py, ctx, constraint)?;
        let parts = constraint_to_parts(py, full_constraint, Some(ctx.clone().into_any().unbind()))?;
        let parts_b = parts.bind(py);
        let mut errors: Vec<PyObject> = Vec::new();
        let err_cls = api_error(py, "LiquidTypeCheckingFailedRelation")?;
        for i in 0..parts_b.len() {
            let tup = parts_b.get_item(i)?;
            let vc = tup.get_item(0)?.unbind();
            let loc = tup.get_item(1)?.unbind();
            let err = err_cls.bind(py).call1((
                ctx.clone().into_any().unbind(),
                term.clone_ref(py),
                expected_type.clone_ref(py),
                vc,
                loc,
            ))?;
            errors.push(err.unbind());
        }
        Ok(errors)
    })();

    match type_errors_result {
        Ok(errs) => {
            for e in errs {
                out.append(e)?;
            }
        }
        Err(e) => {
            let core_err_cls = py.import_bound("aeon.facade.api")?.getattr("CoreTypeCheckingError")?;
            let val = e.value_bound(py);
            if val.is_instance(&core_err_cls)? {
                let val_obj: PyObject = val.clone().into_any().unbind();
                out.append(val_obj)?;
                return Ok(out.unbind());
            }
            return Err(e);
        }
    }

    let lin_errors = crate::linearity::check_linearity(py, term, Some(ctx))?;
    let lin_b = lin_errors.bind(py);
    for i in 0..lin_b.len() {
        out.append(lin_b.get_item(i)?)?;
    }
    Ok(out.unbind())
}

#[allow(dead_code)]
fn _silence(_d: &PyDict, _t: &Type, _l: &Term) {
    fn _t() {
        let _ = mk_liquid_and;
    }
}
type Type = crate::types::Type;
