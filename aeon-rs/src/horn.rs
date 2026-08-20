//! Horn-clause solver (port of `aeon.verification.horn`).
//!
//! Everything pure lives here in Rust. The qualifier-candidate generation
//! still leans on the Python liquid type-checker (`aeon.typechecking.liquid`)
//! and the qualifier extraction (`aeon.typechecking.qualifiers`) — Rust calls
//! back into those modules dynamically. Once the typechecker itself is ported
//! those callbacks will drop out.

use std::collections::HashMap;

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::builders::{
    new_abstraction_type_mult, new_conjunction, new_implication, new_liquid_app,
    new_liquid_constraint, new_liquid_horn_application, new_liquid_literal_bool,
    new_liquid_var, new_refined_type, new_reflected_function_declaration,
    new_refinement_polymorphism, new_type_constructor, new_type_polymorphism,
    new_uninterpreted_function_declaration,
};
use crate::helpers::{constraint_builder, end as helpers_end, imp as helpers_imp};
use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidVar,
};
use crate::name::Name;
use crate::smt_z3::smt_valid;
use crate::substitutions::substitution_in_liquid;
use crate::types::{
    AbstractionType, ExistentialType, RefinedType, RefinementPolymorphism, Top, TypeConstructor,
    TypePolymorphism, TypeVar,
};
use crate::vcs::{
    Conjunction, Implication, LiquidConstraint, ReflectedFunctionDeclaration,
    UninterpretedFunctionDeclaration,
};

// =============================================================================
// smt_base_type — used by the synthesizer modules.
// =============================================================================

#[pyfunction]
pub fn smt_base_type(py: Python<'_>, ty: PyObject) -> PyResult<Option<String>> {
    let bound = ty.bind(py);
    if bound.is_instance_of::<AbstractionType>() {
        return Ok(None);
    }
    if bound.is_instance_of::<TypeConstructor>() {
        return Ok(Some(bound.str()?.to_string()));
    }
    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let inner = rt.borrow().type_.clone_ref(py);
        return smt_base_type(py, inner);
    }
    Ok(None)
}

// =============================================================================
// fresh — rebuild a type with every LiquidHornApplication replaced by a fresh
// horn binder. The typing context is consulted only for its `vars()` snapshot.
// =============================================================================

#[pyfunction]
pub fn fresh(py: Python<'_>, context: PyObject, ty: PyObject) -> PyResult<PyObject> {
    let bound = ty.bind(py);

    if let Ok(rt) = bound.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let inner_ty = rt.type_.clone_ref(py);
        let refinement = rt.refinement.clone_ref(py);
        drop(rt);
        if refinement.bind(py).is_instance_of::<LiquidHornApplication>() {
            let fresh_v = crate::name::next_fresh_id(py)?;
            let vname = Py::new(py, Name { name: "√".to_string(), id: fresh_v })?;
            let fresh_h = crate::name::next_fresh_id(py)?;
            let hole_name = Py::new(py, Name { name: "hole".to_string(), id: fresh_h })?;

            // Build [(LiquidVar(n), t) for (n, t) in context.vars() + [(vname, ty.type)] if isinstance(t, TypeConstructor)]
            let vars_obj = context.call_method0(py, "vars")?;
            let argtypes = PyList::empty_bound(py);
            let vars_list = vars_obj.bind(py).downcast::<PyList>()?;
            for i in 0..vars_list.len() {
                let tup = vars_list.get_item(i)?;
                let n: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
                let t: PyObject = tup.get_item(1)?.unbind();
                if t.bind(py).is_instance_of::<TypeConstructor>() {
                    let lv = new_liquid_var(py, n, crate::loc::default_location(py))?;
                    argtypes.append(PyTuple::new_bound(py, &[lv, t]))?;
                }
            }
            // append the fresh binder's own (vname, ty.type)
            {
                let lv = new_liquid_var(py, vname.clone_ref(py), crate::loc::default_location(py))?;
                argtypes.append(PyTuple::new_bound(py, &[lv, inner_ty.clone_ref(py)]))?;
            }

            let horn = new_liquid_horn_application(
                py,
                hole_name,
                argtypes.unbind(),
                crate::loc::default_location(py),
            )?;
            return new_refined_type(
                py,
                vname,
                inner_ty,
                horn,
                crate::loc::default_location(py),
            );
        }
        // Otherwise: leave the type unchanged.
        return Ok(ty);
    }

    if bound.is_instance_of::<Top>() || bound.is_instance_of::<TypeVar>() {
        return Ok(ty);
    }
    if let Ok(at) = bound.downcast::<AbstractionType>() {
        let at = at.borrow();
        let name = at.var_name.clone_ref(py);
        let aty = at.var_type.clone_ref(py);
        let rty = at.type_.clone_ref(py);
        let mult = at.multiplicity.clone_ref(py);
        let loc = at.loc.clone_ref(py);
        drop(at);
        let sp = fresh(py, context.clone_ref(py), aty.clone_ref(py))?;
        let new_ctx = context.call_method1(py, "with_var", (name.clone_ref(py), aty))?;
        let tp = fresh(py, new_ctx, rty)?;
        return new_abstraction_type_mult(py, name, sp, tp, loc, mult);
    }
    if let Ok(tp) = bound.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let name = tp.name.clone_ref(py);
        let kind = tp.kind.clone_ref(py);
        let body = tp.body.clone_ref(py);
        let loc = tp.loc.clone_ref(py);
        drop(tp);
        let nb = fresh(py, context, body)?;
        return new_type_polymorphism(py, name, kind, nb, loc);
    }
    if let Ok(rp) = bound.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let name = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        let loc = rp.loc.clone_ref(py);
        drop(rp);
        let ns = fresh(py, context.clone_ref(py), sort)?;
        let nb = fresh(py, context, body)?;
        return new_refinement_polymorphism(py, name, ns, nb, loc);
    }
    if let Ok(tc) = bound.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let name = tc.name.clone_ref(py);
        let args = tc.args.clone_ref(py);
        let loc = tc.loc.clone_ref(py);
        drop(tc);
        let new_args = PyList::empty_bound(py);
        let args_b = args.bind(py);
        for i in 0..args_b.len() {
            let a = args_b.get_item(i)?.unbind();
            new_args.append(fresh(py, context.clone_ref(py), a)?)?;
        }
        return new_type_constructor(py, name, new_args.unbind(), loc);
    }
    if let Ok(et) = bound.downcast::<ExistentialType>() {
        let et = et.borrow();
        let binders = et.binders.clone_ref(py);
        let body = et.body.clone_ref(py);
        let loc = et.loc.clone_ref(py);
        drop(et);
        let mut ext_ctx = context;
        let new_binders = PyList::empty_bound(py);
        let binders_b = binders.bind(py);
        for i in 0..binders_b.len() {
            let tup = binders_b.get_item(i)?;
            let bn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let bt: PyObject = tup.get_item(1)?.unbind();
            let fresh_bt = fresh(py, ext_ctx.clone_ref(py), bt.clone_ref(py))?;
            new_binders.append(PyTuple::new_bound(py, &[bn.clone_ref(py).into_any(), fresh_bt.clone_ref(py)]))?;
            ext_ctx = ext_ctx.call_method1(py, "with_var", (bn, fresh_bt))?;
        }
        let new_body = fresh(py, ext_ctx, body)?;
        // ExistentialType expects a tuple of binders.
        let binders_tuple = PyTuple::new_bound(py, new_binders.iter()).unbind();
        return crate::builders::new_existential_type(py, binders_tuple, new_body, loc);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Type not freshable: {} ({})",
        bound.repr()?.to_string(),
        bound.get_type().name()?,
    )))
}

// =============================================================================
// obtain_holes / contains_horn — pure walks.
// =============================================================================

fn collect_holes(py: Python<'_>, t: PyObject, out: &Bound<'_, PyList>) -> PyResult<()> {
    let bound = t.bind(py);
    if bound.is_instance_of::<LiquidHornApplication>() {
        out.append(t)?;
        return Ok(());
    }
    if bound.is_instance_of::<LiquidLiteralBool>()
        || bound.is_instance_of::<LiquidLiteralInt>()
        || bound.is_instance_of::<LiquidLiteralFloat>()
        || bound.is_instance_of::<LiquidLiteralString>()
        || bound.is_instance_of::<LiquidVar>()
    {
        return Ok(());
    }
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        let args = app.args.bind(py);
        for i in 0..args.len() {
            let a = args.get_item(i)?.unbind();
            collect_holes(py, a, out)?;
        }
        return Ok(());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unknown term type: {}",
        bound.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn obtain_holes(py: Python<'_>, t: PyObject) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    collect_holes(py, t, &out)?;
    Ok(out.unbind())
}

fn collect_holes_constraint(py: Python<'_>, c: PyObject, out: &Bound<'_, PyList>) -> PyResult<()> {
    let bound = c.bind(py);
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        drop(conj);
        collect_holes_constraint(py, c1, out)?;
        return collect_holes_constraint(py, c2, out);
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        drop(imp);
        collect_holes(py, pred, out)?;
        return collect_holes_constraint(py, seq, out);
    }
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let expr = lc.borrow().expr.clone_ref(py);
        return collect_holes(py, expr, out);
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let seq = u.borrow().seq.clone_ref(py);
        return collect_holes_constraint(py, seq, out);
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let seq = r.borrow().seq.clone_ref(py);
        return collect_holes_constraint(py, seq, out);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "obtain_holes_constraint: {}",
        bound.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn obtain_holes_constraint(py: Python<'_>, c: PyObject) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    collect_holes_constraint(py, c, &out)?;
    Ok(out.unbind())
}

#[pyfunction]
pub fn contains_horn(py: Python<'_>, t: PyObject) -> PyResult<bool> {
    let bound = t.bind(py);
    if bound.is_instance_of::<LiquidLiteralBool>()
        || bound.is_instance_of::<LiquidLiteralInt>()
        || bound.is_instance_of::<LiquidLiteralFloat>()
        || bound.is_instance_of::<LiquidLiteralString>()
        || bound.is_instance_of::<LiquidVar>()
    {
        return Ok(false);
    }
    if bound.is_instance_of::<LiquidHornApplication>() {
        return Ok(true);
    }
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        let args = app.args.bind(py);
        for i in 0..args.len() {
            let a = args.get_item(i)?.unbind();
            if !contains_horn(py, a)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "contains_horn: {}",
        bound.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn contains_horn_constraint(py: Python<'_>, c: PyObject) -> PyResult<bool> {
    let bound = c.bind(py);
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let expr = lc.borrow().expr.clone_ref(py);
        return contains_horn(py, expr);
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        drop(conj);
        Ok(contains_horn_constraint(py, c1)? || contains_horn_constraint(py, c2)?)
    } else if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        drop(imp);
        Ok(contains_horn(py, pred)? || contains_horn_constraint(py, seq)?)
    } else if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let seq = u.borrow().seq.clone_ref(py);
        contains_horn_constraint(py, seq)
    } else if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let body = r.borrow().body.clone_ref(py);
        let seq = r.borrow().seq.clone_ref(py);
        Ok(contains_horn(py, body)? || contains_horn_constraint(py, seq)?)
    } else {
        Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "contains_horn_constraint: {}",
            bound.repr()?.to_string()
        )))
    }
}

#[pyfunction]
pub fn wellformed_horn(py: Python<'_>, predicate: PyObject) -> PyResult<bool> {
    if !contains_horn(py, predicate.clone_ref(py))? {
        return Ok(true);
    }
    let bound = predicate.bind(py);
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        let args = app.args.bind(py);
        // Python checks `predicate.fun == "&&"` — that's loose (Name vs str)
        // but we faithfully replicate: name "&&", left side has no horn,
        // right side is a LiquidHornApplication.
        let fun_n = app.fun.borrow(py);
        if fun_n.name == "&&" && args.len() == 2 {
            drop(fun_n);
            let a0 = args.get_item(0)?.unbind();
            let a1 = args.get_item(1)?;
            if !contains_horn(py, a0)? && a1.is_instance_of::<LiquidHornApplication>() {
                return Ok(true);
            }
        }
        return Ok(false);
    }
    if bound.is_instance_of::<LiquidHornApplication>() {
        return Ok(true);
    }
    Ok(false)
}

// =============================================================================
// mk_arg / merge_assignments
// =============================================================================

#[pyfunction]
pub fn mk_arg(py: Python<'_>, i: i64) -> PyResult<Py<Name>> {
    Py::new(py, Name { name: format!("arg_{}", i), id: 0 })
}

#[pyfunction]
pub fn merge_assignments(py: Python<'_>, xs: Py<PyList>) -> PyResult<PyObject> {
    use crate::smt_ctx::mk_liquid_and;
    let mut acc: PyObject = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
    let xs_b = xs.bind(py);
    for i in 0..xs_b.len() {
        let item = xs_b.get_item(i)?.unbind();
        acc = mk_liquid_and(py, acc, item)?;
    }
    Ok(acc)
}

// =============================================================================
// split / has_k_head / flat / simpl / build_forall_implication
// =============================================================================

#[pyfunction]
pub fn split(py: Python<'_>, c: PyObject) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    split_into(py, c, &out)?;
    Ok(out.unbind())
}

fn split_into(py: Python<'_>, c: PyObject, out: &Bound<'_, PyList>) -> PyResult<()> {
    let bound = c.bind(py);
    if bound.is_instance_of::<LiquidConstraint>() {
        out.append(c)?;
        return Ok(());
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        drop(conj);
        split_into(py, c1, out)?;
        return split_into(py, c2, out);
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let name = imp.name.clone_ref(py);
        let base = imp.base.clone_ref(py);
        let pre = imp.pred.clone_ref(py);
        let post = imp.seq.clone_ref(py);
        drop(imp);
        let inner = PyList::empty_bound(py);
        split_into(py, post, &inner)?;
        for i in 0..inner.len() {
            let cp = inner.get_item(i)?.unbind();
            let wrapped = new_implication(
                py,
                name.clone_ref(py),
                base.clone_ref(py),
                pre.clone_ref(py),
                cp,
                None,
            )?;
            out.append(wrapped)?;
        }
        return Ok(());
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let u = u.borrow();
        let name = u.name.clone_ref(py);
        let ty = u.type_.clone_ref(py);
        let seq = u.seq.clone_ref(py);
        drop(u);
        let inner = PyList::empty_bound(py);
        split_into(py, seq, &inner)?;
        for i in 0..inner.len() {
            let cp = inner.get_item(i)?.unbind();
            out.append(new_uninterpreted_function_declaration(
                py,
                name.clone_ref(py),
                ty.clone_ref(py),
                cp,
            )?)?;
        }
        return Ok(());
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let r = r.borrow();
        let name = r.name.clone_ref(py);
        let ty = r.type_.clone_ref(py);
        let params = r.params.clone_ref(py);
        let body = r.body.clone_ref(py);
        let seq = r.seq.clone_ref(py);
        drop(r);
        let inner = PyList::empty_bound(py);
        split_into(py, seq, &inner)?;
        for i in 0..inner.len() {
            let cp = inner.get_item(i)?.unbind();
            out.append(new_reflected_function_declaration(
                py,
                name.clone_ref(py),
                ty.clone_ref(py),
                params.clone_ref(py),
                body.clone_ref(py),
                cp,
            )?)?;
        }
        return Ok(());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "split: unsupported {}",
        bound.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn has_k_head(py: Python<'_>, c: PyObject) -> PyResult<bool> {
    let bound = c.bind(py);
    if bound.is_instance_of::<Conjunction>() {
        return Err(pyo3::exceptions::PyAssertionError::new_err(
            "has_k_head: Conjunction unexpected (flat() should have eliminated it)",
        ));
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let post = imp.borrow().seq.clone_ref(py);
        return has_k_head(py, post);
    }
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let e = lc.borrow().expr.clone_ref(py);
        return Ok(e.bind(py).is_instance_of::<LiquidHornApplication>());
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let seq = u.borrow().seq.clone_ref(py);
        return has_k_head(py, seq);
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let seq = r.borrow().seq.clone_ref(py);
        return has_k_head(py, seq);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unknown constraint type: {}",
        bound.repr()?.to_string()
    )))
}

fn build_forall_implication(
    py: Python<'_>,
    vs: &[(Py<Name>, PyObject)],
    p: PyObject,
    c: PyObject,
) -> PyResult<PyObject> {
    if vs.is_empty() {
        return Ok(c);
    }
    let (last_n, last_t) = vs.last().unwrap();
    let mut cf = new_implication(
        py,
        last_n.clone_ref(py),
        last_t.clone_ref(py),
        p,
        c,
        None,
    )?;
    for (n, t) in vs[..vs.len() - 1].iter().rev() {
        let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
        cf = new_implication(py, n.clone_ref(py), t.clone_ref(py), lb, cf, None)?;
    }
    Ok(cf)
}

fn simpl_rec(
    py: Python<'_>,
    mut vs: Vec<(Py<Name>, PyObject)>,
    p: PyObject,
    c: PyObject,
) -> PyResult<PyObject> {
    use crate::smt_ctx::mk_liquid_and;
    if let Ok(imp) = c.bind(py).downcast::<Implication>() {
        let imp = imp.borrow();
        let name = imp.name.clone_ref(py);
        let base = imp.base.clone_ref(py);
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        drop(imp);
        vs.push((name, base));
        let new_p = mk_liquid_and(py, p, pred)?;
        return simpl_rec(py, vs, new_p, seq);
    }
    build_forall_implication(py, &vs, p, c)
}

#[pyfunction]
pub fn flat(py: Python<'_>, c: PyObject) -> PyResult<Py<PyList>> {
    let splits = split(py, c)?;
    let out = PyList::empty_bound(py);
    let splits_b = splits.bind(py);
    for i in 0..splits_b.len() {
        let cp = splits_b.get_item(i)?.unbind();
        let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
        let simplified = simpl_rec(py, Vec::new(), lb, cp)?;
        out.append(simplified)?;
    }
    Ok(out.unbind())
}

// =============================================================================
// apply / apply_liquid / apply_constraint / fill_horn_arguments
// =============================================================================

#[pyfunction]
pub fn fill_horn_arguments(
    py: Python<'_>,
    h: PyObject,
    candidate: PyObject,
) -> PyResult<PyObject> {
    let h_b = h.bind(py);
    let horn = h_b.downcast::<LiquidHornApplication>()?.borrow();
    let argtypes = horn.argtypes.bind(py);
    let mut cur = candidate;
    for i in 0..argtypes.len() {
        let tup = argtypes.get_item(i)?;
        let n = tup.get_item(0)?.unbind();
        let arg_i = Py::new(py, Name { name: format!("arg_{}", i), id: 0 })?;
        cur = substitution_in_liquid(py, cur, n, arg_i)?;
    }
    Ok(cur)
}

#[pyfunction]
pub fn apply_liquid(py: Python<'_>, assign: PyObject, c: PyObject) -> PyResult<PyObject> {
    let bound = c.bind(py);
    if let Ok(horn) = bound.downcast::<LiquidHornApplication>() {
        let horn = horn.borrow();
        let h_name = horn.name.clone_ref(py);
        let assign_d = assign.bind(py).downcast::<pyo3::types::PyDict>()?;
        if let Some(ne) = assign_d.get_item(h_name.clone_ref(py))? {
            let ne_list = ne.downcast::<PyList>()?.clone().unbind();
            let merged = merge_assignments(py, ne_list)?;
            drop(horn);
            let h_obj = c.clone_ref(py);
            return fill_horn_arguments(py, h_obj, merged);
        }
        drop(horn);
        return Ok(c);
    }
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let loc = app.loc.clone_ref(py);
        let args = app.args.bind(py);
        let new_args = PyList::empty_bound(py);
        for i in 0..args.len() {
            let a = args.get_item(i)?.unbind();
            new_args.append(apply_liquid(py, assign.clone_ref(py), a)?)?;
        }
        drop(app);
        return new_liquid_app(py, fun, new_args.unbind(), loc);
    }
    Ok(c)
}

#[pyfunction]
pub fn apply_constraint(py: Python<'_>, assign: PyObject, c: PyObject) -> PyResult<PyObject> {
    let bound = c.bind(py);
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let expr = lc.borrow().expr.clone_ref(py);
        let new_expr = apply_liquid(py, assign, expr)?;
        return new_liquid_constraint(py, new_expr, None);
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        drop(conj);
        let n1 = apply_constraint(py, assign.clone_ref(py), c1)?;
        let n2 = apply_constraint(py, assign, c2)?;
        return new_conjunction(py, n1, n2, None);
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let name = imp.name.clone_ref(py);
        let base = imp.base.clone_ref(py);
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        drop(imp);
        let np = apply_liquid(py, assign.clone_ref(py), pred)?;
        let nseq = apply_constraint(py, assign, seq)?;
        return new_implication(py, name, base, np, nseq, None);
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let u = u.borrow();
        let name = u.name.clone_ref(py);
        let ty = u.type_.clone_ref(py);
        let seq = u.seq.clone_ref(py);
        drop(u);
        let nseq = apply_constraint(py, assign, seq)?;
        return new_uninterpreted_function_declaration(py, name, ty, nseq);
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let r = r.borrow();
        let name = r.name.clone_ref(py);
        let ty = r.type_.clone_ref(py);
        let params = r.params.clone_ref(py);
        let body = r.body.clone_ref(py);
        let seq = r.seq.clone_ref(py);
        drop(r);
        let nbody = apply_liquid(py, assign.clone_ref(py), body)?;
        let nseq = apply_constraint(py, assign, seq)?;
        return new_reflected_function_declaration(py, name, ty, params, nbody, nseq);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "apply_constraint: unsupported {}",
        c.bind(py).repr()?.to_string()
    )))
}

#[pyfunction]
pub fn apply(py: Python<'_>, assign: PyObject, c: PyObject) -> PyResult<PyObject> {
    use crate::liquid::LiquidTerm;
    let bound = c.bind(py);
    if bound.is_instance_of::<crate::vcs::Constraint>() {
        return apply_constraint(py, assign, c);
    }
    if bound.is_instance_of::<LiquidTerm>() {
        return apply_liquid(py, assign, c);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "apply: not a Constraint or LiquidTerm: {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// extract_components_of_imp / weaken / fixpoint / solve
// =============================================================================

#[pyfunction]
pub fn extract_components_of_imp(
    py: Python<'_>,
    c: PyObject,
) -> PyResult<Py<PyTuple>> {
    use crate::smt_ctx::mk_liquid_and;
    let bound = c.bind(py);

    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let u = u.borrow();
        let name = u.name.clone_ref(py);
        let base = u.type_.clone_ref(py);
        let post = u.seq.clone_ref(py);
        drop(u);
        let inner = extract_components_of_imp(py, post)?;
        let inner_b = inner.bind(py);
        let vs1 = inner_b.get_item(0)?;
        let ph = inner_b.get_item(1)?;
        let new_vs = PyList::empty_bound(py);
        let entry = PyTuple::new_bound(py, &[name.into_any(), base]);
        new_vs.append(entry)?;
        let vs1_b = vs1.downcast::<PyList>()?;
        for i in 0..vs1_b.len() {
            new_vs.append(vs1_b.get_item(i)?)?;
        }
        return Ok(PyTuple::new_bound(py, &[new_vs.into_any().unbind(), ph.unbind()]).unbind());
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let r = r.borrow();
        let name = r.name.clone_ref(py);
        let base = r.type_.clone_ref(py);
        let post = r.seq.clone_ref(py);
        drop(r);
        let inner = extract_components_of_imp(py, post)?;
        let inner_b = inner.bind(py);
        let vs1 = inner_b.get_item(0)?;
        let ph = inner_b.get_item(1)?;
        let new_vs = PyList::empty_bound(py);
        let entry = PyTuple::new_bound(py, &[name.into_any(), base]);
        new_vs.append(entry)?;
        let vs1_b = vs1.downcast::<PyList>()?;
        for i in 0..vs1_b.len() {
            new_vs.append(vs1_b.get_item(i)?)?;
        }
        return Ok(PyTuple::new_bound(py, &[new_vs.into_any().unbind(), ph.unbind()]).unbind());
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let name = imp.name.clone_ref(py);
        let base = imp.base.clone_ref(py);
        let pre = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        drop(imp);
        let inner = extract_components_of_imp(py, seq)?;
        let inner_b = inner.bind(py);
        let vs1 = inner_b.get_item(0)?;
        let ph = inner_b.get_item(1)?;
        let ph_tup = ph.downcast::<PyTuple>()?;
        let p = ph_tup.get_item(0)?.unbind();
        let h = ph_tup.get_item(1)?.unbind();
        let new_vs = PyList::empty_bound(py);
        let entry = PyTuple::new_bound(py, &[name.into_any(), base]);
        new_vs.append(entry)?;
        let vs1_b = vs1.downcast::<PyList>()?;
        for i in 0..vs1_b.len() {
            new_vs.append(vs1_b.get_item(i)?)?;
        }
        let new_p = mk_liquid_and(py, pre, p)?;
        let new_ph = PyTuple::new_bound(py, &[new_p, h]).into_any().unbind();
        return Ok(PyTuple::new_bound(py, &[new_vs.into_any().unbind(), new_ph]).unbind());
    }
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let e = lc.borrow().expr.clone_ref(py);
        let vs_empty = PyList::empty_bound(py);
        let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
        let ph = PyTuple::new_bound(py, &[lb, e]).into_any().unbind();
        return Ok(PyTuple::new_bound(py, &[vs_empty.into_any().unbind(), ph]).unbind());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "extract_components_of_imp: {}",
        bound.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn weaken(py: Python<'_>, assign: PyObject, c: PyObject) -> PyResult<PyObject> {
    let comps = extract_components_of_imp(py, c)?;
    let comps_b = comps.bind(py);
    let vs_obj = comps_b.get_item(0)?;
    let ph = comps_b.get_item(1)?;
    let ph_tup = ph.downcast::<PyTuple>()?;
    let p = ph_tup.get_item(0)?.unbind();
    let h = ph_tup.get_item(1)?.unbind();

    // h is a LiquidHornApplication.
    let h_b = h.bind(py);
    let horn = h_b.downcast::<LiquidHornApplication>()?.borrow();
    let h_name = horn.name.clone_ref(py);
    drop(horn);

    let assign_d = assign.bind(py).downcast::<pyo3::types::PyDict>()?;
    let current_rep = assign_d
        .get_item(h_name.clone_ref(py))?
        .ok_or_else(|| pyo3::exceptions::PyAssertionError::new_err("weaken: hole name not in assignment"))?;
    let current_rep_b = current_rep.downcast::<PyList>()?;

    // Filter the current candidate list.
    let vs_list: Py<PyList> = vs_obj.downcast::<PyList>()?.clone().unbind();
    let p_applied = apply_liquid(py, assign.clone_ref(py), p)?;
    let kept = PyList::empty_bound(py);
    for i in 0..current_rep_b.len() {
        let q = current_rep_b.get_item(i)?.unbind();
        let qp = fill_horn_arguments(py, h.clone_ref(py), q.clone_ref(py))?;
        let inner = helpers_imp(py, p_applied.clone_ref(py), helpers_end(py, qp)?)?;
        let nc = constraint_builder(py, vs_list.clone_ref(py), inner)?;
        if smt_valid(py, nc)? {
            kept.append(q)?;
        }
    }

    // Build the updated assignment dict.
    let out = pyo3::types::PyDict::new_bound(py);
    for (k, v) in assign_d.iter() {
        let k_name = k.downcast::<Name>()?.borrow();
        let h_borrow = h_name.borrow(py);
        if k_name.name == h_borrow.name && k_name.id == h_borrow.id {
            drop(k_name);
            drop(h_borrow);
            out.set_item(k, kept.clone().unbind())?;
        } else {
            drop(k_name);
            drop(h_borrow);
            out.set_item(k, v)?;
        }
    }
    Ok(out.into_any().unbind())
}

#[pyfunction]
pub fn fixpoint(py: Python<'_>, cs: Py<PyList>, assign: PyObject) -> PyResult<PyObject> {
    let mut current_assign = assign;
    loop {
        let mut ncs: Vec<PyObject> = Vec::new();
        let cs_b = cs.bind(py);
        for i in 0..cs_b.len() {
            let c = cs_b.get_item(i)?.unbind();
            let applied = apply(py, current_assign.clone_ref(py), c.clone_ref(py))?;
            if !smt_valid(py, applied)? {
                ncs.push(c);
            }
        }
        if ncs.is_empty() {
            return Ok(current_assign);
        }
        current_assign = weaken(py, current_assign, ncs.into_iter().next().unwrap())?;
    }
}

// =============================================================================
// Qualifier-candidate generation — depends on the Python liquid type-checker
// and qualifier extractor. Wrapped here so all of horn lives in Rust; the
// callbacks drop away once those modules are ported too.
// =============================================================================

/// Build the `LiquidTypeCheckingContext` for a hole — Rust-native version.
/// `liquid_prelude` (the built-in operator signatures) is the only Python
/// data still consulted; the rest goes through `liquid_check::lower_context`.
fn rs_liquid_typechecking_ctx_for_hole(
    py: Python<'_>,
    typing_ctx: Option<PyObject>,
    hole: PyObject,
) -> PyResult<Py<crate::liquid_check::LiquidTypeCheckingContext>> {
    let horn_b = hole.bind(py);
    let horn = horn_b.downcast::<LiquidHornApplication>()?.borrow();
    let argtypes = horn.argtypes.clone_ref(py);
    drop(horn);

    let liq_ops_mod = py.import_bound("aeon.core.liquid_ops")?;
    let liquid_prelude = liq_ops_mod.getattr("liquid_prelude")?;
    let liquid_prelude_dict = liquid_prelude.downcast::<pyo3::types::PyDict>()?;

    // vars_h = {mk_arg(i): ty for i, (_, ty) in enumerate(hole.argtypes)}
    let vars_h = pyo3::types::PyDict::new_bound(py);
    let at = argtypes.bind(py);
    for i in 0..at.len() {
        let tup = at.get_item(i)?;
        let ty = tup.get_item(1)?;
        let arg_i = Py::new(py, Name { name: format!("arg_{}", i), id: 0 })?;
        vars_h.set_item(arg_i, ty)?;
    }

    let mut ctx_obj = match typing_ctx {
        Some(t) => {
            let bound = t.bind(py).downcast::<crate::typectx::TypingContext>()?.clone();
            let lc = crate::liquid_check::lower_context(py, &bound)?;
            Py::new(py, lc)?
        }
        None => {
            // Default ctx (no Python typing context) — builtin core types,
            // empty vars, just the liquid prelude functions.
            let known_types = PyList::empty_bound(py);
            for n in ["Unit", "Bool", "Int", "Float", "String", "Set", "Tensor", "GpuConfig"] {
                let nm = Py::new(py, Name { name: n.to_string(), id: 0 })?;
                let empty = PyList::empty_bound(py).unbind();
                let tc =
                    new_type_constructor(py, nm, empty, crate::loc::default_location(py))?;
                known_types.append(tc)?;
            }
            let empty_vars = pyo3::types::PyDict::new_bound(py);
            let empty_funs = pyo3::types::PyDict::new_bound(py);
            Py::new(
                py,
                crate::liquid_check::LiquidTypeCheckingContext::py_new(
                    known_types.unbind(),
                    empty_vars.unbind(),
                    empty_funs.unbind(),
                ),
            )?
        }
    };

    // Merge the liquid_prelude functions in, then layer the hole's vars.
    // Build a fresh ctx so we don't mutate the typing_ctx-derived one.
    let merged_functions = pyo3::types::PyDict::new_bound(py);
    for (k, v) in liquid_prelude_dict.iter() {
        merged_functions.set_item(k, v)?;
    }
    {
        let cur = ctx_obj.borrow(py);
        for (k, v) in cur.functions.bind(py).iter() {
            if !merged_functions.contains(k.clone())? {
                merged_functions.set_item(k, v)?;
            }
        }
    }
    let known_types = {
        let cur = ctx_obj.borrow(py);
        cur.known_types.clone_ref(py)
    };
    ctx_obj = Py::new(
        py,
        crate::liquid_check::LiquidTypeCheckingContext::py_new(
            known_types,
            vars_h.unbind(),
            merged_functions.unbind(),
        ),
    )?;
    Ok(ctx_obj)
}

fn rs_check_liquid(
    py: Python<'_>,
    ctx: &Py<crate::liquid_check::LiquidTypeCheckingContext>,
    term: PyObject,
    ty: PyObject,
) -> PyResult<bool> {
    crate::liquid_check::check_liquid(py, ctx.bind(py), term, ty)
}

fn t_bool(py: Python<'_>) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: "Bool".to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    new_type_constructor(py, n, empty, crate::loc::default_location(py))
}

fn liquid_var_names_in_term(
    py: Python<'_>,
    t: PyObject,
    out: &mut HashMap<String, ()>,
) -> PyResult<()> {
    let bound = t.bind(py);
    if let Ok(v) = bound.downcast::<LiquidVar>() {
        let nm = v.borrow().name.borrow(py).name.clone();
        out.insert(nm, ());
        return Ok(());
    }
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        let args = app.args.bind(py);
        for i in 0..args.len() {
            let a = args.get_item(i)?.unbind();
            liquid_var_names_in_term(py, a, out)?;
        }
    }
    Ok(())
}

#[pyfunction]
pub fn adapt_qualifier_to_hole(
    py: Python<'_>,
    hole: PyObject,
    q: PyObject,
) -> PyResult<Option<PyObject>> {
    let horn_b = hole.bind(py);
    let horn = horn_b.downcast::<LiquidHornApplication>()?.borrow();
    let argtypes = horn.argtypes.clone_ref(py);
    drop(horn);

    let mut t = q;
    let at = argtypes.bind(py);
    for i in 0..at.len() {
        let tup = at.get_item(i)?;
        let slot = tup.get_item(0)?;
        if let Ok(lv) = slot.downcast::<LiquidVar>() {
            let nm = lv.borrow().name.clone_ref(py);
            let arg_i = Py::new(py, Name { name: format!("arg_{}", i), id: 0 })?;
            let arg_var = new_liquid_var(py, arg_i, crate::loc::default_location(py))?;
            t = substitution_in_liquid(py, t, arg_var, nm)?;
        } else {
            return Ok(None);
        }
    }

    let mut names = HashMap::new();
    liquid_var_names_in_term(py, t.clone_ref(py), &mut names)?;
    for nm in names.keys() {
        if !nm.starts_with("arg_") {
            return Ok(None);
        }
    }
    Ok(Some(t))
}

#[pyfunction]
#[pyo3(signature = (typing_ctx, hole, atoms))]
pub fn build_qualifier_candidates(
    py: Python<'_>,
    typing_ctx: Option<PyObject>,
    hole: PyObject,
    atoms: PyObject,
) -> PyResult<Py<PyList>> {
    let atoms_b = atoms.bind(py);
    if atoms_b.len()? == 0 {
        return Ok(PyList::empty_bound(py).unbind());
    }
    let liq_ctx = rs_liquid_typechecking_ctx_for_hole(py, typing_ctx, hole.clone_ref(py))?;
    let tb = t_bool(py)?;
    let out = PyList::empty_bound(py);
    let mut seen: Vec<PyObject> = Vec::new();
    for q in atoms_b.iter()? {
        let q_obj: PyObject = q?.unbind();
        let adapted = adapt_qualifier_to_hole(py, hole.clone_ref(py), q_obj)?;
        let Some(a) = adapted else {
            continue;
        };
        if !rs_check_liquid(py, &liq_ctx, a.clone_ref(py), tb.clone_ref(py))? {
            continue;
        }
        let mut already = false;
        for s in &seen {
            if a.bind(py).eq(s.bind(py))? {
                already = true;
                break;
            }
        }
        if already {
            continue;
        }
        seen.push(a.clone_ref(py));
        out.append(a)?;
    }
    Ok(out.unbind())
}

/// Public Python entry point — mirrors `aeon.verification.horn.get_possible_args`.
/// Returns a list of argument-lists (each candidate spelled out as a list of
/// LiquidTerms). The Python signature is `(vars, arity)`; we extract the arity
/// from the kwarg and the count of `vars` from the input list.
#[pyfunction]
pub fn get_possible_args(
    py: Python<'_>,
    vars: Py<PyList>,
    arity: usize,
) -> PyResult<Py<PyList>> {
    let n = vars.bind(py).len();
    let mut combos: Vec<Vec<PyObject>> = Vec::new();
    get_possible_args_inner(py, n, arity, &mut combos)?;
    let out = PyList::empty_bound(py);
    for combo in combos {
        out.append(PyList::new_bound(py, &combo))?;
    }
    Ok(out.unbind())
}

fn get_possible_args_inner(
    py: Python<'_>,
    n_argtypes: usize,
    arity: usize,
    out: &mut Vec<Vec<PyObject>>,
) -> PyResult<()> {
    if arity == 0 {
        out.push(Vec::new());
        return Ok(());
    }
    let mut base: Vec<Vec<PyObject>> = Vec::new();
    get_possible_args_inner(py, n_argtypes, arity - 1, &mut base)?;
    let lb_true = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
    let lb_false = new_liquid_literal_bool(py, false, crate::loc::default_location(py))?;
    let zero_obj: PyObject = Py::new(
        py,
        (
            crate::liquid::LiquidLiteralInt {
                value: 0,
                loc: crate::loc::default_location(py),
            },
            crate::liquid::LiquidTerm,
        ),
    )?
    .into_any();
    let one_obj: PyObject = Py::new(
        py,
        (
            crate::liquid::LiquidLiteralInt {
                value: 1,
                loc: crate::loc::default_location(py),
            },
            crate::liquid::LiquidTerm,
        ),
    )?
    .into_any();

    for b in &base {
        for i in 0..n_argtypes {
            let arg_i = Py::new(py, Name { name: format!("arg_{}", i), id: 0 })?;
            let lv = new_liquid_var(py, arg_i, crate::loc::default_location(py))?;
            for prefix in [
                lv,
                lb_true.clone_ref(py),
                lb_false.clone_ref(py),
                zero_obj.clone_ref(py),
                one_obj.clone_ref(py),
            ] {
                let mut combo = vec![prefix];
                for x in b {
                    combo.push(x.clone_ref(py));
                }
                out.push(combo);
            }
        }
    }
    Ok(())
}

fn build_possible_assignment(py: Python<'_>, hole: PyObject) -> PyResult<Py<PyList>> {
    let horn_b = hole.bind(py);
    let horn = horn_b.downcast::<LiquidHornApplication>()?.borrow();
    let argtypes = horn.argtypes.clone_ref(py);
    drop(horn);

    // Pull the liquid prelude (still Python data) and build a Rust-native
    // LiquidTypeCheckingContext from it.
    let liq_ops_mod = py.import_bound("aeon.core.liquid_ops")?;
    let liquid_prelude = liq_ops_mod.getattr("liquid_prelude")?;
    let liquid_prelude_dict = liquid_prelude.downcast::<pyo3::types::PyDict>()?;

    let known_types = PyList::empty_bound(py);
    for n in ["Unit", "Bool", "Int", "Float", "String", "Set", "Tensor", "GpuConfig"] {
        let nm = Py::new(py, Name { name: n.to_string(), id: 0 })?;
        let empty = PyList::empty_bound(py).unbind();
        known_types.append(new_type_constructor(
            py,
            nm,
            empty,
            crate::loc::default_location(py),
        )?)?;
    }
    let vars_h = pyo3::types::PyDict::new_bound(py);
    let at = argtypes.bind(py);
    for i in 0..at.len() {
        let tup = at.get_item(i)?;
        let ty = tup.get_item(1)?;
        let arg_i = Py::new(py, Name { name: format!("arg_{}", i), id: 0 })?;
        vars_h.set_item(arg_i, ty)?;
    }
    let functions = pyo3::types::PyDict::new_bound(py);
    for (k, v) in liquid_prelude_dict.iter() {
        functions.set_item(k, v)?;
    }
    let ctx = Py::new(
        py,
        crate::liquid_check::LiquidTypeCheckingContext::py_new(
            known_types.unbind(),
            vars_h.unbind(),
            functions.unbind(),
        ),
    )?;

    let out = PyList::empty_bound(py);
    let n_argtypes = at.len();
    let tb = t_bool(py)?;
    for (fname_obj, ftype_obj) in liquid_prelude_dict.iter() {
        let ftype = ftype_obj.downcast::<PyList>()?;
        let arity = ftype.len() - 1;
        let mut combos: Vec<Vec<PyObject>> = Vec::new();
        get_possible_args_inner(py, n_argtypes, arity, &mut combos)?;
        for args in combos {
            let any_var = args.iter().any(|a| a.bind(py).downcast::<LiquidVar>().is_ok());
            if !any_var {
                continue;
            }
            let arg_list = PyList::new_bound(py, &args).unbind();
            let fname: Py<Name> = fname_obj.downcast::<Name>()?.clone().unbind();
            let app = new_liquid_app(py, fname, arg_list, crate::loc::default_location(py))?;
            if rs_check_liquid(py, &ctx, app.clone_ref(py), tb.clone_ref(py))? {
                out.append(app)?;
            }
        }
    }
    Ok(out.unbind())
}

#[pyfunction]
#[pyo3(signature = (c, typing_ctx = None, qualifier_atoms = None))]
pub fn build_initial_assignment(
    py: Python<'_>,
    c: PyObject,
    typing_ctx: Option<PyObject>,
    qualifier_atoms: Option<PyObject>,
) -> PyResult<PyObject> {
    let atoms_obj: PyObject = match qualifier_atoms {
        Some(a) => a,
        None => pyo3::types::PyFrozenSet::empty_bound(py)?.into_any().unbind(),
    };
    let holes = obtain_holes_constraint(py, c)?;
    let assign = pyo3::types::PyDict::new_bound(py);
    let holes_b = holes.bind(py);
    for i in 0..holes_b.len() {
        let h = holes_b.get_item(i)?.unbind();
        let h_b = h.bind(py);
        let horn = h_b.downcast::<LiquidHornApplication>()?.borrow();
        let h_name = horn.name.clone_ref(py);
        drop(horn);
        if assign.contains(h_name.clone_ref(py))? {
            continue;
        }
        let prelude = build_possible_assignment(py, h.clone_ref(py))?;
        let extra = build_qualifier_candidates(
            py,
            typing_ctx.as_ref().map(|t| t.clone_ref(py)),
            h.clone_ref(py),
            atoms_obj.clone_ref(py),
        )?;
        // Result = prelude + [c for c in extra if c not in prelude_set]
        let prelude_b = prelude.bind(py);
        let combined = PyList::empty_bound(py);
        for j in 0..prelude_b.len() {
            combined.append(prelude_b.get_item(j)?)?;
        }
        let extra_b = extra.bind(py);
        for j in 0..extra_b.len() {
            let candidate = extra_b.get_item(j)?;
            let mut in_prelude = false;
            for k in 0..prelude_b.len() {
                if candidate.eq(prelude_b.get_item(k)?)? {
                    in_prelude = true;
                    break;
                }
            }
            if !in_prelude {
                combined.append(candidate)?;
            }
        }
        assign.set_item(h_name, combined.unbind())?;
    }
    Ok(assign.into_any().unbind())
}

// =============================================================================
// solve — top-level entry point.
// =============================================================================

#[pyfunction]
#[pyo3(signature = (c, typing_ctx = None, qualifier_atoms = None))]
pub fn solve(
    py: Python<'_>,
    c: PyObject,
    typing_ctx: Option<PyObject>,
    qualifier_atoms: Option<PyObject>,
) -> PyResult<bool> {
    if !contains_horn_constraint(py, c.clone_ref(py))? {
        return smt_valid(py, c);
    }
    // Qualifier atoms — use the Rust-native extractor.
    let atoms: PyObject = match qualifier_atoms {
        Some(a) => a,
        None => match &typing_ctx {
            Some(t) => {
                let bound = t.bind(py).downcast::<crate::typectx::TypingContext>()?.clone();
                let frozen = crate::qualifiers::extract_qualifier_atoms(py, &bound, None, None, 512)?;
                frozen.into_any()
            }
            None => pyo3::types::PyFrozenSet::empty_bound(py)?.into_any().unbind(),
        },
    };

    let cs = flat(py, c.clone_ref(py))?;
    let cs_b = cs.bind(py);
    let csk = PyList::empty_bound(py);
    let csp = PyList::empty_bound(py);
    for i in 0..cs_b.len() {
        let item = cs_b.get_item(i)?.unbind();
        if has_k_head(py, item.clone_ref(py))? {
            csk.append(item)?;
        } else {
            csp.append(item)?;
        }
    }

    let assignment0 = build_initial_assignment(
        py,
        c,
        typing_ctx.as_ref().map(|t| t.clone_ref(py)),
        Some(atoms),
    )?;
    let subst = fixpoint(py, csk.unbind(), assignment0)?;

    // Reduce csp via Conjunction, then apply subst and call smt_valid.
    let mut acc: PyObject = {
        let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
        new_liquid_constraint(py, lb, None)?
    };
    let csp_unbound = csp.unbind();
    let csp_b = csp_unbound.bind(py);
    for i in 0..csp_b.len() {
        let pi = csp_b.get_item(i)?.unbind();
        acc = new_conjunction(py, acc, pi, None)?;
    }
    let c_final = apply(py, subst, acc)?;
    smt_valid(py, c_final)
}
