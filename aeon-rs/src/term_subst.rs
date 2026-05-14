//! Rust ports of the remaining recursive substitution walks in
//! aeon.core.substitutions:
//!
//!  - substitute_vartype_in_term     (Term -> Term)   propagates substitute_vartype
//!  - substitution_liquid_in_type    (Type -> Type)   substitutes a LiquidTerm at refinement positions
//!  - substitution_liquid_in_term    (Term -> Term)   propagates substitution_liquid_in_type
//!  - instantiate_refinement_with_horn_in_liquid     (LiquidTerm -> LiquidTerm)
//!  - instantiate_refinement_with_horn_in_type       (Type -> Type)
//!  - substitution                   (Term -> Term)   replaces Var(name)/Hole(name) with rep
//!
//! `substitute_vartype` itself lives in substitutions.rs. liquefy/inline_lets
//! and instantiate_refinement_in_{liquid,type} (which depend on liquefy) stay
//! in Python — they form a mutually-recursive cluster better moved together.

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::builders::{
    name_eq, new_abstraction, new_abstraction_type, new_annotation, new_application, new_if,
    new_let, new_literal, new_liquid_app, new_liquid_horn_application, new_rec, new_refined_type,
    new_refinement_abstraction, new_refinement_application, new_refinement_polymorphism,
    new_type_abstraction, new_type_application, new_type_constructor, new_type_polymorphism,
};
use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidVar,
};
use crate::name::Name;
use crate::substitutions::substitute_vartype;
use crate::terms::{
    Abstraction, Annotation, Application, Hole, If, Let, Literal, Rec, RefinementAbstraction,
    RefinementApplication, TypeAbstraction, TypeApplication, Var,
};
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, TypeConstructor, TypePolymorphism,
    TypeVar,
};

// =============================================================================
// substitute_vartype_in_term: propagate substitute_vartype through a Term.
// =============================================================================

#[pyfunction]
pub fn substitute_vartype_in_term(
    py: Python<'_>,
    t: PyObject,
    rep: PyObject,
    name: Py<Name>,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if bound.is_instance_of::<Literal>()
        || bound.is_instance_of::<Var>()
        || bound.is_instance_of::<Hole>()
    {
        return Ok(t);
    }
    if let Ok(app) = bound.downcast::<Application>() {
        let app = app.borrow();
        let nf = substitute_vartype_in_term(py, app.fun.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let na = substitute_vartype_in_term(py, app.arg.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_application(py, nf, na, app.loc.clone_ref(py));
    }
    if let Ok(ab) = bound.downcast::<Abstraction>() {
        let ab = ab.borrow();
        let nb = substitute_vartype_in_term(py, ab.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_abstraction(py, ab.var_name.clone_ref(py), nb, ab.loc.clone_ref(py));
    }
    if let Ok(le) = bound.downcast::<Let>() {
        let le = le.borrow();
        let nv = substitute_vartype_in_term(py, le.var_value.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nb = substitute_vartype_in_term(py, le.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_let(py, le.var_name.clone_ref(py), nv, nb, le.loc.clone_ref(py));
    }
    if let Ok(rc) = bound.downcast::<Rec>() {
        let rc = rc.borrow();
        let nv = substitute_vartype_in_term(py, rc.var_value.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nt = substitute_vartype(py, rc.var_type.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nb = substitute_vartype_in_term(py, rc.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_rec(
            py,
            rc.var_name.clone_ref(py),
            nt,
            nv,
            nb,
            rc.decreasing_by.clone_ref(py),
            rc.loc.clone_ref(py),
        );
    }
    if let Ok(an) = bound.downcast::<Annotation>() {
        let an = an.borrow();
        let nt = substitute_vartype(py, an.type_.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let ne = substitute_vartype_in_term(py, an.expr.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_annotation(py, ne, nt, an.loc.clone_ref(py));
    }
    if let Ok(ife) = bound.downcast::<If>() {
        let ife = ife.borrow();
        let nc = substitute_vartype_in_term(py, ife.cond.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nt = substitute_vartype_in_term(py, ife.then.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let no = substitute_vartype_in_term(py, ife.otherwise.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_if(py, nc, nt, no, ife.loc.clone_ref(py));
    }
    if let Ok(ta) = bound.downcast::<TypeAbstraction>() {
        let ta = ta.borrow();
        let nb = substitute_vartype_in_term(py, ta.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_type_abstraction(py, ta.name.clone_ref(py), ta.kind.clone_ref(py), nb, ta.loc.clone_ref(py));
    }
    if let Ok(tap) = bound.downcast::<TypeApplication>() {
        let tap = tap.borrow();
        let nb = substitute_vartype_in_term(py, tap.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nt = substitute_vartype(py, tap.type_.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_type_application(py, nb, nt, tap.loc.clone_ref(py));
    }
    if let Ok(rapp) = bound.downcast::<RefinementApplication>() {
        let rapp = rapp.borrow();
        let nb = substitute_vartype_in_term(py, rapp.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nr = substitute_vartype_in_term(py, rapp.refinement.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_refinement_application(py, nb, nr, rapp.loc.clone_ref(py));
    }
    if let Ok(rab) = bound.downcast::<RefinementAbstraction>() {
        let rab = rab.borrow();
        let ns = substitute_vartype(py, rab.sort.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nb = substitute_vartype_in_term(py, rab.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_refinement_abstraction(py, rab.name.clone_ref(py), ns, nb, rab.loc.clone_ref(py));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "substitute_vartype_in_term: unknown term {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// substitution_liquid_in_type: substitute a LiquidTerm at refinement positions.
// Mirrors Python: `case Top() | TypeConstructor(_) | TypeVar(_): return t` —
// any TypeConstructor returns as-is (the explicit later case is unreachable).
// =============================================================================

#[pyfunction]
pub fn substitution_liquid_in_type(
    py: Python<'_>,
    t: PyObject,
    rep: PyObject,
    name: Py<Name>,
) -> PyResult<PyObject> {
    use crate::substitutions::substitution_in_liquid;
    let bound = t.bind(py);

    if bound.is_instance_of::<Top>()
        || bound.is_instance_of::<TypeConstructor>()
        || bound.is_instance_of::<TypeVar>()
    {
        return Ok(t);
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        if name_eq(py, &at.var_name, &name) {
            return Ok(t);
        }
        let nv = substitution_liquid_in_type(py, at.var_type.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nt = substitution_liquid_in_type(py, at.type_.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_abstraction_type(py, at.var_name.clone_ref(py), nv, nt, at.loc.clone_ref(py));
    }
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        if name_eq(py, &rt.name, &name) {
            return Ok(t);
        }
        let nr = substitution_in_liquid(py, rt.refinement.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_refined_type(py, rt.name.clone_ref(py), rt.type_.clone_ref(py), nr, rt.loc.clone_ref(py));
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let nb = substitution_liquid_in_type(py, tp.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_type_polymorphism(py, tp.name.clone_ref(py), tp.kind.clone_ref(py), nb, tp.loc.clone_ref(py));
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        if name_eq(py, &rp.name, &name) {
            return Ok(t);
        }
        let ns = substitution_liquid_in_type(py, rp.sort.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nb = substitution_liquid_in_type(py, rp.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_refinement_polymorphism(py, rp.name.clone_ref(py), ns, nb, rp.loc.clone_ref(py));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "substitution_liquid_in_type: unknown type {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// substitution_liquid_in_term: propagate substitution_liquid_in_type through Term.
// =============================================================================

#[pyfunction]
pub fn substitution_liquid_in_term(
    py: Python<'_>,
    t: PyObject,
    rep: PyObject,
    name: Py<Name>,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if let Ok(lit) = bound.downcast::<Literal>() {
        let lit = lit.borrow();
        let nt = substitution_liquid_in_type(py, lit.type_.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_literal(py, lit.value.clone_ref(py), nt, lit.loc.clone_ref(py));
    }
    if bound.is_instance_of::<Var>() || bound.is_instance_of::<Hole>() {
        return Ok(t);
    }
    if let Ok(app) = bound.downcast::<Application>() {
        let app = app.borrow();
        let nf = substitution_liquid_in_term(py, app.fun.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let na = substitution_liquid_in_term(py, app.arg.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_application(py, nf, na, app.loc.clone_ref(py));
    }
    if let Ok(ab) = bound.downcast::<Abstraction>() {
        let ab = ab.borrow();
        let nb = substitution_liquid_in_term(py, ab.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_abstraction(py, ab.var_name.clone_ref(py), nb, ab.loc.clone_ref(py));
    }
    if let Ok(le) = bound.downcast::<Let>() {
        let le = le.borrow();
        let nv = substitution_liquid_in_term(py, le.var_value.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nb = substitution_liquid_in_term(py, le.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_let(py, le.var_name.clone_ref(py), nv, nb, le.loc.clone_ref(py));
    }
    if let Ok(rc) = bound.downcast::<Rec>() {
        let rc = rc.borrow();
        let nt = substitution_liquid_in_type(py, rc.var_type.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nv = substitution_liquid_in_term(py, rc.var_value.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nb = substitution_liquid_in_term(py, rc.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_rec(
            py,
            rc.var_name.clone_ref(py),
            nt,
            nv,
            nb,
            rc.decreasing_by.clone_ref(py),
            rc.loc.clone_ref(py),
        );
    }
    if let Ok(an) = bound.downcast::<Annotation>() {
        let an = an.borrow();
        let nt = substitution_liquid_in_type(py, an.type_.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let ne = substitution_liquid_in_term(py, an.expr.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_annotation(py, ne, nt, an.loc.clone_ref(py));
    }
    if let Ok(ife) = bound.downcast::<If>() {
        let ife = ife.borrow();
        let nc = substitution_liquid_in_term(py, ife.cond.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nt = substitution_liquid_in_term(py, ife.then.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let no = substitution_liquid_in_term(py, ife.otherwise.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_if(py, nc, nt, no, ife.loc.clone_ref(py));
    }
    if let Ok(ta) = bound.downcast::<TypeAbstraction>() {
        let ta = ta.borrow();
        let nb = substitution_liquid_in_term(py, ta.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_type_abstraction(py, ta.name.clone_ref(py), ta.kind.clone_ref(py), nb, ta.loc.clone_ref(py));
    }
    if let Ok(rab) = bound.downcast::<RefinementAbstraction>() {
        let rab = rab.borrow();
        let ns = substitution_liquid_in_type(py, rab.sort.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nb = substitution_liquid_in_term(py, rab.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_refinement_abstraction(py, rab.name.clone_ref(py), ns, nb, rab.loc.clone_ref(py));
    }
    if let Ok(tap) = bound.downcast::<TypeApplication>() {
        let tap = tap.borrow();
        let nb = substitution_liquid_in_term(py, tap.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nt = substitution_liquid_in_type(py, tap.type_.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_type_application(py, nb, nt, tap.loc.clone_ref(py));
    }
    if let Ok(rapp) = bound.downcast::<RefinementApplication>() {
        let rapp = rapp.borrow();
        let nb = substitution_liquid_in_term(py, rapp.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nr = substitution_liquid_in_term(py, rapp.refinement.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_refinement_application(py, nb, nr, rapp.loc.clone_ref(py));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "substitution_liquid_in_term: unknown term {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// instantiate_refinement_with_horn_in_liquid
// =============================================================================

#[pyfunction]
pub fn instantiate_refinement_with_horn_in_liquid(
    py: Python<'_>,
    t: PyObject,
    pred_name: Py<Name>,
    sort: PyObject,
    horn_name: Py<Name>,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if bound.is_instance_of::<LiquidVar>()
        || bound.is_instance_of::<LiquidLiteralBool>()
        || bound.is_instance_of::<LiquidLiteralInt>()
        || bound.is_instance_of::<LiquidLiteralFloat>()
        || bound.is_instance_of::<LiquidLiteralString>()
    {
        return Ok(t);
    }
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        if name_eq(py, &app.fun, &pred_name) {
            let sort_bound = sort.bind(py);
            if !(sort_bound.is_instance_of::<TypeConstructor>()
                || sort_bound.is_instance_of::<TypeVar>())
            {
                return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                    "instantiate_refinement_with_horn_in_liquid: sort must be TypeConstructor or TypeVar, got {}",
                    sort_bound.repr()?.to_string()
                )));
            }
            let args = app.args.bind(py);
            let argtypes = PyList::empty_bound(py);
            for i in 0..args.len() {
                let a = args.get_item(i)?;
                let tup = PyTuple::new_bound(py, &[a.into(), sort.clone_ref(py)]);
                argtypes.append(tup)?;
            }
            return new_liquid_horn_application(py, horn_name.clone_ref(py), argtypes.unbind(), app.loc.clone_ref(py));
        }
        let args = app.args.bind(py);
        let new_args = PyList::empty_bound(py);
        for i in 0..args.len() {
            let a = args.get_item(i)?;
            let na = instantiate_refinement_with_horn_in_liquid(
                py,
                a.into(),
                pred_name.clone_ref(py),
                sort.clone_ref(py),
                horn_name.clone_ref(py),
            )?;
            new_args.append(na)?;
        }
        return new_liquid_app(py, app.fun.clone_ref(py), new_args.unbind(), app.loc.clone_ref(py));
    }
    if let Ok(h) = bound.downcast::<LiquidHornApplication>() {
        let h = h.borrow();
        let argtypes = h.argtypes.bind(py);
        let new_argtypes = PyList::empty_bound(py);
        for i in 0..argtypes.len() {
            let item = argtypes.get_item(i)?;
            let tup = item.downcast::<PyTuple>().map_err(|_| {
                pyo3::exceptions::PyAssertionError::new_err("argtypes items must be tuples")
            })?;
            let a = tup.get_item(0)?;
            let ty = tup.get_item(1)?;
            let na = instantiate_refinement_with_horn_in_liquid(
                py,
                a.into(),
                pred_name.clone_ref(py),
                sort.clone_ref(py),
                horn_name.clone_ref(py),
            )?;
            let new_tup = PyTuple::new_bound(py, &[na, ty.into()]);
            new_argtypes.append(new_tup)?;
        }
        return new_liquid_horn_application(py, h.name.clone_ref(py), new_argtypes.unbind(), h.loc.clone_ref(py));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "instantiate_refinement_with_horn_in_liquid: unknown liquid {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// instantiate_refinement_with_horn_in_type
// =============================================================================

#[pyfunction]
pub fn instantiate_refinement_with_horn_in_type(
    py: Python<'_>,
    t: PyObject,
    pred_name: Py<Name>,
    sort: PyObject,
    horn_name: Py<Name>,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if bound.is_instance_of::<Top>() || bound.is_instance_of::<TypeVar>() {
        return Ok(t);
    }
    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let args = tc.args.bind(py);
        let new_args = PyList::empty_bound(py);
        for i in 0..args.len() {
            let a = args.get_item(i)?;
            let na = instantiate_refinement_with_horn_in_type(
                py,
                a.into(),
                pred_name.clone_ref(py),
                sort.clone_ref(py),
                horn_name.clone_ref(py),
            )?;
            new_args.append(na)?;
        }
        return new_type_constructor(py, tc.name.clone_ref(py), new_args.unbind(), tc.loc.clone_ref(py));
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let nv = instantiate_refinement_with_horn_in_type(
            py,
            at.var_type.clone_ref(py),
            pred_name.clone_ref(py),
            sort.clone_ref(py),
            horn_name.clone_ref(py),
        )?;
        let nt = instantiate_refinement_with_horn_in_type(
            py,
            at.type_.clone_ref(py),
            pred_name.clone_ref(py),
            sort.clone_ref(py),
            horn_name.clone_ref(py),
        )?;
        return new_abstraction_type(py, at.var_name.clone_ref(py), nv, nt, at.loc.clone_ref(py));
    }
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let nity = instantiate_refinement_with_horn_in_type(
            py,
            rt.type_.clone_ref(py),
            pred_name.clone_ref(py),
            sort.clone_ref(py),
            horn_name.clone_ref(py),
        )?;
        let nity_bound = nity.bind(py);
        if !(nity_bound.is_instance_of::<TypeConstructor>()
            || nity_bound.is_instance_of::<TypeVar>())
        {
            return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                "instantiate_refinement_with_horn_in_type: inner type must be TypeConstructor or TypeVar, got {}",
                nity_bound.repr()?.to_string()
            )));
        }
        let new_ref = instantiate_refinement_with_horn_in_liquid(
            py,
            rt.refinement.clone_ref(py),
            pred_name.clone_ref(py),
            sort.clone_ref(py),
            horn_name.clone_ref(py),
        )?;
        return new_refined_type(py, rt.name.clone_ref(py), nity, new_ref, rt.loc.clone_ref(py));
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let nb = instantiate_refinement_with_horn_in_type(
            py,
            tp.body.clone_ref(py),
            pred_name.clone_ref(py),
            sort.clone_ref(py),
            horn_name.clone_ref(py),
        )?;
        return new_type_polymorphism(py, tp.name.clone_ref(py), tp.kind.clone_ref(py), nb, tp.loc.clone_ref(py));
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let ns = instantiate_refinement_with_horn_in_type(
            py,
            rp.sort.clone_ref(py),
            pred_name.clone_ref(py),
            sort.clone_ref(py),
            horn_name.clone_ref(py),
        )?;
        let nb = instantiate_refinement_with_horn_in_type(
            py,
            rp.body.clone_ref(py),
            pred_name.clone_ref(py),
            sort.clone_ref(py),
            horn_name.clone_ref(py),
        )?;
        return new_refinement_polymorphism(py, rp.name.clone_ref(py), ns, nb, rp.loc.clone_ref(py));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "instantiate_refinement_with_horn_in_type: unknown type {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// substitution: substitutes name in Term t with the new replacement term rep.
// =============================================================================

#[pyfunction]
pub fn substitution(
    py: Python<'_>,
    t: PyObject,
    rep: PyObject,
    name: Py<Name>,
) -> PyResult<PyObject> {
    let bound = t.bind(py);

    if bound.is_instance_of::<Literal>() {
        return Ok(t);
    }
    if let Ok(v) = bound.downcast::<Var>() {
        if name_eq(py, &v.borrow().name, &name) {
            return Ok(rep);
        }
        return Ok(t);
    }
    if let Ok(h) = bound.downcast::<Hole>() {
        if name_eq(py, &h.borrow().name, &name) {
            return Ok(rep);
        }
        return Ok(t);
    }
    if let Ok(app) = bound.downcast::<Application>() {
        let app = app.borrow();
        let nf = substitution(py, app.fun.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let na = substitution(py, app.arg.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_application(py, nf, na, app.loc.clone_ref(py));
    }
    if let Ok(ab) = bound.downcast::<Abstraction>() {
        let ab = ab.borrow();
        if name_eq(py, &ab.var_name, &name) {
            return Ok(t);
        }
        let nb = substitution(py, ab.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_abstraction(py, ab.var_name.clone_ref(py), nb, ab.loc.clone_ref(py));
    }
    if let Ok(le) = bound.downcast::<Let>() {
        let le = le.borrow();
        let (nv, nb) = if name_eq(py, &le.var_name, &name) {
            (le.var_value.clone_ref(py), le.body.clone_ref(py))
        } else {
            (
                substitution(py, le.var_value.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?,
                substitution(py, le.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?,
            )
        };
        return new_let(py, le.var_name.clone_ref(py), nv, nb, le.loc.clone_ref(py));
    }
    if let Ok(rc) = bound.downcast::<Rec>() {
        let rc = rc.borrow();
        let (nv, nb) = if name_eq(py, &rc.var_name, &name) {
            (rc.var_value.clone_ref(py), rc.body.clone_ref(py))
        } else {
            (
                substitution(py, rc.var_value.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?,
                substitution(py, rc.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?,
            )
        };
        return new_rec(
            py,
            rc.var_name.clone_ref(py),
            rc.var_type.clone_ref(py),
            nv,
            nb,
            rc.decreasing_by.clone_ref(py),
            rc.loc.clone_ref(py),
        );
    }
    if let Ok(an) = bound.downcast::<Annotation>() {
        let an = an.borrow();
        let nb = substitution(py, an.expr.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_annotation(py, nb, an.type_.clone_ref(py), an.loc.clone_ref(py));
    }
    if let Ok(ife) = bound.downcast::<If>() {
        let ife = ife.borrow();
        let nc = substitution(py, ife.cond.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nt = substitution(py, ife.then.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let no = substitution(py, ife.otherwise.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_if(py, nc, nt, no, ife.loc.clone_ref(py));
    }
    if let Ok(tap) = bound.downcast::<TypeApplication>() {
        let tap = tap.borrow();
        let ne = substitution(py, tap.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_type_application(py, ne, tap.type_.clone_ref(py), tap.loc.clone_ref(py));
    }
    if let Ok(ta) = bound.downcast::<TypeAbstraction>() {
        let ta = ta.borrow();
        let nb = substitution(py, ta.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_type_abstraction(py, ta.name.clone_ref(py), ta.kind.clone_ref(py), nb, ta.loc.clone_ref(py));
    }
    if let Ok(rab) = bound.downcast::<RefinementAbstraction>() {
        let rab = rab.borrow();
        let nb = substitution(py, rab.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_refinement_abstraction(py, rab.name.clone_ref(py), rab.sort.clone_ref(py), nb, rab.loc.clone_ref(py));
    }
    if let Ok(rapp) = bound.downcast::<RefinementApplication>() {
        let rapp = rapp.borrow();
        let nb = substitution(py, rapp.body.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        let nr = substitution(py, rapp.refinement.clone_ref(py), rep.clone_ref(py), name.clone_ref(py))?;
        return new_refinement_application(py, nb, nr, rapp.loc.clone_ref(py));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "substitution: unsupported term {}",
        bound.repr()?.to_string()
    )))
}
