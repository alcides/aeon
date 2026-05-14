//! The mutually-recursive `liquefy` / `inline_lets` cluster from
//! aeon.core.substitutions, ported to Rust:
//!
//!  - inline_lets                    (Term -> Term)
//!  - uncurry                        (Term, [LiquidTerm] -> LiquidTerm | None)
//!  - liquefy_app / _rec / _let / _if / _ann
//!  - liquefy                        (Term -> LiquidTerm | None)
//!  - instantiate_refinement_in_liquid   (LiquidTerm -> LiquidTerm)
//!  - instantiate_refinement_in_type     (Type -> Type)
//!  - substitution_in_type               (Type -> Type)
//!
//! These form a tight cycle: liquefy calls inline_lets, inline_lets calls
//! substitution (Rust) + substitute_vartype_in_term (Rust), liquefy_* call
//! liquefy and substitution_in_liquid (Rust). Moving them as one unit.

use pyo3::prelude::*;
use pyo3::types::PyList;

use crate::builders::{
    name_eq, new_abstraction, new_abstraction_type, new_application, new_if,
    new_liquid_app, new_liquid_horn_application, new_liquid_literal_bool, new_liquid_literal_float,
    new_liquid_literal_int, new_liquid_literal_string, new_liquid_var, new_refined_type,
    new_refinement_polymorphism, new_type_application, new_type_polymorphism, new_var,
};
use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidVar,
};
use crate::name::Name;
use crate::substitutions::substitution_in_liquid;
use crate::term_subst::{substitute_vartype_in_term, substitution};
use crate::terms::{
    Abstraction, Annotation, Application, Hole, If, Let, Literal, Rec, RefinementAbstraction,
    RefinementApplication, TypeAbstraction, TypeApplication, Var,
};
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, TypeConstructor, TypePolymorphism,
    TypeVar,
};

/// True if `tc` is a TypeConstructor whose name is `(expected, 0)`.
fn tc_named(py: Python<'_>, obj: &Bound<'_, PyAny>, expected: &str) -> bool {
    if let Ok(tc) = obj.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let n = tc.name.borrow(py);
        return n.id == 0 && n.name == expected;
    }
    false
}

// =============================================================================
// inline_lets: beta-reduce all lets / applied lambdas / type applications.
// =============================================================================

#[pyfunction]
pub fn inline_lets(py: Python<'_>, t: PyObject) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if let Ok(le) = bound.downcast::<Let>() {
        let le = le.borrow();
        let subst = substitution(
            py,
            le.body.clone_ref(py),
            le.var_value.clone_ref(py),
            le.var_name.clone_ref(py),
        )?;
        return inline_lets(py, subst);
    }
    if let Ok(rc) = bound.downcast::<Rec>() {
        let rc = rc.borrow();
        let subst = substitution(
            py,
            rc.body.clone_ref(py),
            rc.var_value.clone_ref(py),
            rc.var_name.clone_ref(py),
        )?;
        return inline_lets(py, subst);
    }
    if let Ok(app) = bound.downcast::<Application>() {
        let app = app.borrow();
        let fun_bound = app.fun.bind(py);
        // Application(Annotation(Abstraction(var_name, body), _), arg)
        if let Ok(ann) = fun_bound.downcast::<Annotation>() {
            let ann = ann.borrow();
            if let Ok(ab) = ann.expr.bind(py).downcast::<Abstraction>() {
                let ab = ab.borrow();
                let subst = substitution(
                    py,
                    ab.body.clone_ref(py),
                    app.arg.clone_ref(py),
                    ab.var_name.clone_ref(py),
                )?;
                return inline_lets(py, subst);
            }
        }
        // Application(Abstraction(var_name, body), arg)
        if let Ok(ab) = fun_bound.downcast::<Abstraction>() {
            let ab = ab.borrow();
            let subst = substitution(
                py,
                ab.body.clone_ref(py),
                app.arg.clone_ref(py),
                ab.var_name.clone_ref(py),
            )?;
            return inline_lets(py, subst);
        }
        // Application(fun, arg, loc) — general
        let nf = inline_lets(py, app.fun.clone_ref(py))?;
        let na = inline_lets(py, app.arg.clone_ref(py))?;
        return new_application(py, nf, na, app.loc.clone_ref(py));
    }
    if let Ok(ab) = bound.downcast::<Abstraction>() {
        let ab = ab.borrow();
        let nb = inline_lets(py, ab.body.clone_ref(py))?;
        return new_abstraction(py, ab.var_name.clone_ref(py), nb, ab.loc.clone_ref(py));
    }
    if let Ok(ife) = bound.downcast::<If>() {
        let ife = ife.borrow();
        let nc = inline_lets(py, ife.cond.clone_ref(py))?;
        let nt = inline_lets(py, ife.then.clone_ref(py))?;
        let no = inline_lets(py, ife.otherwise.clone_ref(py))?;
        return new_if(py, nc, nt, no, ife.loc.clone_ref(py));
    }
    if let Ok(tap) = bound.downcast::<TypeApplication>() {
        let tap = tap.borrow();
        // TypeApplication(TypeAbstraction(name, _, body), ty, loc)
        if let Ok(ta) = tap.body.bind(py).downcast::<TypeAbstraction>() {
            let ta = ta.borrow();
            let subst = substitute_vartype_in_term(
                py,
                ta.body.clone_ref(py),
                tap.type_.clone_ref(py),
                ta.name.clone_ref(py),
            )?;
            return inline_lets(py, subst);
        }
        // TypeApplication(expr, ty, loc) — general
        let ne = inline_lets(py, tap.body.clone_ref(py))?;
        return new_type_application(py, ne, tap.type_.clone_ref(py), tap.loc.clone_ref(py));
    }
    // case _: return t
    Ok(t)
}

// =============================================================================
// uncurry: peel TypeApplication/RefinementApplication and curried Applications
// into a flat LiquidApp. Returns None when an argument can't be liquefied.
// =============================================================================

fn uncurry(py: Python<'_>, t: PyObject, args: Vec<PyObject>) -> PyResult<Option<PyObject>> {
    let bound = t.bind(py);

    if let Ok(tap) = bound.downcast::<TypeApplication>() {
        let tap = tap.borrow();
        return uncurry(py, tap.body.clone_ref(py), args);
    }
    if let Ok(rapp) = bound.downcast::<RefinementApplication>() {
        let rapp = rapp.borrow();
        return uncurry(py, rapp.body.clone_ref(py), args);
    }
    if let Ok(app) = bound.downcast::<Application>() {
        let app = app.borrow();
        match liquefy(py, app.arg.clone_ref(py))? {
            None => Ok(None),
            Some(liquid_arg) => {
                let mut new_args = Vec::with_capacity(args.len() + 1);
                new_args.push(liquid_arg);
                new_args.extend(args);
                uncurry(py, app.fun.clone_ref(py), new_args)
            }
        }
    } else {
        match liquefy(py, t)? {
            None => Ok(None),
            Some(liquid_t) => {
                let lt = liquid_t.bind(py);
                if let Ok(v) = lt.downcast::<LiquidVar>() {
                    let v = v.borrow();
                    let arg_list = PyList::new_bound(py, &args);
                    let r = new_liquid_app(
                        py,
                        v.name.clone_ref(py),
                        arg_list.unbind(),
                        v.loc.clone_ref(py),
                    )?;
                    Ok(Some(r))
                } else {
                    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                        "uncurry: unexpected liquefied term {}",
                        lt.repr()?.to_string()
                    )))
                }
            }
        }
    }
}

fn liquefy_app(py: Python<'_>, app: PyObject) -> PyResult<Option<PyObject>> {
    uncurry(py, app, Vec::new())
}

fn liquefy_rec(py: Python<'_>, rc: &Rec) -> PyResult<Option<PyObject>> {
    let value = liquefy(py, rc.var_value.clone_ref(py))?;
    let body = liquefy(py, rc.body.clone_ref(py))?;
    match (value, body) {
        (Some(value), Some(body)) => {
            Ok(Some(substitution_in_liquid(py, body, value, rc.var_name.clone_ref(py))?))
        }
        _ => Ok(None),
    }
}

fn liquefy_let(py: Python<'_>, le: &Let) -> PyResult<Option<PyObject>> {
    let value = liquefy(py, le.var_value.clone_ref(py))?;
    let body = liquefy(py, le.body.clone_ref(py))?;
    match (value, body) {
        (Some(value), Some(body)) => {
            Ok(Some(substitution_in_liquid(py, body, value, le.var_name.clone_ref(py))?))
        }
        _ => Ok(None),
    }
}

fn liquefy_if(py: Python<'_>, ife: &If) -> PyResult<Option<PyObject>> {
    let co = liquefy(py, ife.cond.clone_ref(py))?;
    let th = liquefy(py, ife.then.clone_ref(py))?;
    let ot = liquefy(py, ife.otherwise.clone_ref(py))?;
    match (co, th, ot) {
        (Some(co), Some(th), Some(ot)) => {
            let ite = Py::new(py, Name { name: "ite".to_string(), id: 0 })?;
            let args = PyList::new_bound(py, &[co, th, ot]);
            Ok(Some(new_liquid_app(py, ite, args.unbind(), ife.loc.clone_ref(py))?))
        }
        _ => Ok(None),
    }
}

// =============================================================================
// liquefy: convert a Term into a LiquidTerm, or None when not expressible.
// =============================================================================

#[pyfunction]
pub fn liquefy(py: Python<'_>, rep: PyObject) -> PyResult<Option<PyObject>> {
    let rep = inline_lets(py, rep)?;
    let bound = rep.bind(py);

    if let Ok(lit) = bound.downcast::<Literal>() {
        let lit = lit.borrow();
        let ty = lit.type_.bind(py);
        if tc_named(py, &ty, "Int") {
            let v: i64 = lit.value.bind(py).extract()?;
            return Ok(Some(new_liquid_literal_int(py, v, lit.loc.clone_ref(py))?));
        }
        if tc_named(py, &ty, "Float") {
            let v: f64 = lit.value.bind(py).extract()?;
            return Ok(Some(new_liquid_literal_float(py, v, lit.loc.clone_ref(py))?));
        }
        if tc_named(py, &ty, "Bool") {
            let v: bool = lit.value.bind(py).extract()?;
            return Ok(Some(new_liquid_literal_bool(py, v, lit.loc.clone_ref(py))?));
        }
        if tc_named(py, &ty, "String") {
            let v: String = lit.value.bind(py).extract()?;
            return Ok(Some(new_liquid_literal_string(py, v, lit.loc.clone_ref(py))?));
        }
        // Literal with an unexpected type — falls through to the error below,
        // mirroring the Python `case _: raise Exception`.
    } else if bound.is_instance_of::<Application>() {
        return liquefy_app(py, rep);
    } else if let Ok(ta) = bound.downcast::<TypeAbstraction>() {
        let ta = ta.borrow();
        return liquefy(py, ta.body.clone_ref(py));
    } else if let Ok(ra) = bound.downcast::<RefinementAbstraction>() {
        let ra = ra.borrow();
        return liquefy(py, ra.body.clone_ref(py));
    } else if let Ok(v) = bound.downcast::<Var>() {
        let v = v.borrow();
        return Ok(Some(new_liquid_var(py, v.name.clone_ref(py), v.loc.clone_ref(py))?));
    } else if let Ok(h) = bound.downcast::<Hole>() {
        let h = h.borrow();
        let empty = PyList::empty_bound(py);
        return Ok(Some(new_liquid_horn_application(
            py,
            h.name.clone_ref(py),
            empty.unbind(),
            h.loc.clone_ref(py),
        )?));
    } else if let Ok(le) = bound.downcast::<Let>() {
        return liquefy_let(py, &le.borrow());
    } else if let Ok(rc) = bound.downcast::<Rec>() {
        return liquefy_rec(py, &rc.borrow());
    } else if let Ok(ife) = bound.downcast::<If>() {
        return liquefy_if(py, &ife.borrow());
    } else if let Ok(an) = bound.downcast::<Annotation>() {
        let an = an.borrow();
        return liquefy(py, an.expr.clone_ref(py));
    } else if let Ok(tap) = bound.downcast::<TypeApplication>() {
        let tap = tap.borrow();
        return liquefy(py, tap.body.clone_ref(py));
    } else if let Ok(rapp) = bound.downcast::<RefinementApplication>() {
        let rapp = rapp.borrow();
        return liquefy(py, rapp.body.clone_ref(py));
    } else if bound.is_instance_of::<Abstraction>() {
        return Ok(None);
    }
    Err(pyo3::exceptions::PyException::new_err(format!(
        "Unable to liquefy {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// instantiate_refinement_in_liquid: inline a predicate's body at applications.
// =============================================================================

#[pyfunction]
pub fn instantiate_refinement_in_liquid(
    py: Python<'_>,
    t: PyObject,
    pred_name: Py<Name>,
    refinement: PyObject,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        let args = app.args.bind(py);
        // pred_name match + single LiquidVar arg => inline the refinement body
        if name_eq(py, &app.fun, &pred_name) && args.len() == 1 {
            let arg0 = args.get_item(0)?;
            if let Ok(lv) = arg0.downcast::<LiquidVar>() {
                let lv = lv.borrow();
                let refn = refinement.bind(py).downcast::<Abstraction>().map_err(|_| {
                    pyo3::exceptions::PyAssertionError::new_err(
                        "instantiate_refinement_in_liquid: refinement must be an Abstraction",
                    )
                })?;
                let refn = refn.borrow();
                let var = new_var(py, lv.name.clone_ref(py), lv.loc.clone_ref(py))?;
                let body_subst =
                    substitution(py, refn.body.clone_ref(py), var, refn.var_name.clone_ref(py))?;
                let body_subst = inline_lets(py, body_subst)?;
                if let Some(liq) = liquefy(py, body_subst)? {
                    return Ok(liq);
                }
            }
        }
        // otherwise: rebuild LiquidApp recursing into args
        let new_args = PyList::empty_bound(py);
        for i in 0..args.len() {
            let a = args.get_item(i)?;
            let na = instantiate_refinement_in_liquid(
                py,
                a.into(),
                pred_name.clone_ref(py),
                refinement.clone_ref(py),
            )?;
            new_args.append(na)?;
        }
        return new_liquid_app(py, app.fun.clone_ref(py), new_args.unbind(), app.loc.clone_ref(py));
    }
    if bound.is_instance_of::<LiquidVar>()
        || bound.is_instance_of::<LiquidLiteralBool>()
        || bound.is_instance_of::<LiquidLiteralInt>()
        || bound.is_instance_of::<LiquidLiteralFloat>()
        || bound.is_instance_of::<LiquidLiteralString>()
    {
        return Ok(t);
    }
    if let Ok(h) = bound.downcast::<LiquidHornApplication>() {
        let h = h.borrow();
        let argtypes = h.argtypes.bind(py);
        let new_argtypes = PyList::empty_bound(py);
        for i in 0..argtypes.len() {
            let item = argtypes.get_item(i)?;
            let tup = item.downcast::<pyo3::types::PyTuple>().map_err(|_| {
                pyo3::exceptions::PyAssertionError::new_err("argtypes items must be tuples")
            })?;
            let a = tup.get_item(0)?;
            let ty = tup.get_item(1)?;
            let na = instantiate_refinement_in_liquid(
                py,
                a.into(),
                pred_name.clone_ref(py),
                refinement.clone_ref(py),
            )?;
            let new_tup = pyo3::types::PyTuple::new_bound(py, &[na, ty.into()]);
            new_argtypes.append(new_tup)?;
        }
        return new_liquid_horn_application(
            py,
            h.name.clone_ref(py),
            new_argtypes.unbind(),
            h.loc.clone_ref(py),
        );
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unknown LiquidTerm {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// instantiate_refinement_in_type: walk a type, inlining the predicate.
// Mirrors Python: `case Top() | TypeConstructor(_) | TypeVar(_): return t`
// — TypeConstructor is returned as-is (no recursion into its args).
// =============================================================================

#[pyfunction]
pub fn instantiate_refinement_in_type(
    py: Python<'_>,
    t: PyObject,
    pred_name: Py<Name>,
    refinement: PyObject,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if bound.is_instance_of::<Top>()
        || bound.is_instance_of::<TypeConstructor>()
        || bound.is_instance_of::<TypeVar>()
    {
        return Ok(t);
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let na = instantiate_refinement_in_type(
            py,
            at.var_type.clone_ref(py),
            pred_name.clone_ref(py),
            refinement.clone_ref(py),
        )?;
        let nr = instantiate_refinement_in_type(
            py,
            at.type_.clone_ref(py),
            pred_name.clone_ref(py),
            refinement.clone_ref(py),
        )?;
        return new_abstraction_type(py, at.var_name.clone_ref(py), na, nr, at.loc.clone_ref(py));
    }
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let ntype = instantiate_refinement_in_type(
            py,
            rt.type_.clone_ref(py),
            pred_name.clone_ref(py),
            refinement.clone_ref(py),
        )?;
        let ntype_bound = ntype.bind(py);
        if !(ntype_bound.is_instance_of::<TypeConstructor>()
            || ntype_bound.is_instance_of::<TypeVar>())
        {
            return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                "instantiate_refinement_in_type: inner type must be TypeConstructor or TypeVar, got {}",
                ntype_bound.repr()?.to_string()
            )));
        }
        let nref = instantiate_refinement_in_liquid(
            py,
            rt.refinement.clone_ref(py),
            pred_name.clone_ref(py),
            refinement.clone_ref(py),
        )?;
        return new_refined_type(py, rt.name.clone_ref(py), ntype, nref, rt.loc.clone_ref(py));
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let nb = instantiate_refinement_in_type(
            py,
            tp.body.clone_ref(py),
            pred_name.clone_ref(py),
            refinement.clone_ref(py),
        )?;
        return new_type_polymorphism(py, tp.name.clone_ref(py), tp.kind.clone_ref(py), nb, tp.loc.clone_ref(py));
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let ns = instantiate_refinement_in_type(
            py,
            rp.sort.clone_ref(py),
            pred_name.clone_ref(py),
            refinement.clone_ref(py),
        )?;
        let nb = instantiate_refinement_in_type(
            py,
            rp.body.clone_ref(py),
            pred_name.clone_ref(py),
            refinement.clone_ref(py),
        )?;
        return new_refinement_polymorphism(py, rp.name.clone_ref(py), ns, nb, rp.loc.clone_ref(py));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unknown type {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// substitution_in_type: substitute `name` in type `t` with term `rep`.
// `rep` is liquefied first; if it can't be, the type is returned unchanged.
// Mirrors Python: `case Top() | TypeConstructor(_) | TypeVar(_): return t`.
// =============================================================================

#[pyfunction]
pub fn substitution_in_type(
    py: Python<'_>,
    t: PyObject,
    rep: PyObject,
    name: Py<Name>,
) -> PyResult<PyObject> {
    let replacement = match liquefy(py, rep)? {
        Some(r) => r,
        None => return Ok(t),
    };

    fn rec(py: Python<'_>, t: PyObject, replacement: &PyObject, name: &Py<Name>) -> PyResult<PyObject> {
        let bound = t.bind(py);

        if bound.is_instance_of::<Top>()
            || bound.is_instance_of::<TypeConstructor>()
            || bound.is_instance_of::<TypeVar>()
        {
            return Ok(t);
        }
        if let Ok(at) = bound.downcast::<AbstractionType>() {
            let at = at.borrow();
            if name_eq(py, &at.var_name, name) {
                return Ok(t);
            }
            let na = rec(py, at.var_type.clone_ref(py), replacement, name)?;
            let nr = rec(py, at.type_.clone_ref(py), replacement, name)?;
            return new_abstraction_type(py, at.var_name.clone_ref(py), na, nr, at.loc.clone_ref(py));
        }
        if let Ok(rt) = bound.downcast::<RefinedType>() {
            let rt = rt.borrow();
            if name_eq(py, &rt.name, name) {
                return Ok(t);
            }
            let nref = substitution_in_liquid(
                py,
                rt.refinement.clone_ref(py),
                replacement.clone_ref(py),
                name.clone_ref(py),
            )?;
            return new_refined_type(py, rt.name.clone_ref(py), rt.type_.clone_ref(py), nref, rt.loc.clone_ref(py));
        }
        if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
            let tp = tp.borrow();
            let nb = rec(py, tp.body.clone_ref(py), replacement, name)?;
            return new_type_polymorphism(py, tp.name.clone_ref(py), tp.kind.clone_ref(py), nb, tp.loc.clone_ref(py));
        }
        Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "substitution_in_type: {} not allowed",
            bound.repr()?.to_string()
        )))
    }

    rec(py, t, &replacement, &name)
}
