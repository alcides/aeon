//! Constraint helpers, simplification, CNF, pretty-printing.
//!
//! Direct port of `aeon.verification.helpers`. The only piece kept on the
//! Python side is `parse_liquid` (and the string overloads of `imp` / `end`)
//! because they call into the lark-based `aeon.core.parser`; the Rust
//! versions here take `LiquidTerm` and `Constraint` directly.

use std::collections::HashSet;

use pyo3::prelude::*;
use pyo3::types::PyList;

use crate::builders::{
    new_conjunction, new_implication, new_liquid_app, new_liquid_constraint,
    new_liquid_literal_bool, new_liquid_var, new_reflected_function_declaration,
    new_refinement_abstraction, new_type_constructor, new_uninterpreted_function_declaration,
};
use crate::liquid::{
    liquid_free_vars, LiquidApp, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidTerm, LiquidVar,
};
use crate::name::Name;
use crate::substitutions::substitution_in_liquid;
use crate::types::{AbstractionType, RefinedType, Top, TypeConstructor, TypeVar};
use crate::vcs::{
    Conjunction, Constraint, Implication, LiquidConstraint, ReflectedFunctionDeclaration,
    UninterpretedFunctionDeclaration,
};

// =============================================================================
// constraint_location
// =============================================================================

/// Clone an `Option<PyObject>` under the GIL. `Option<T>` doesn't implement
/// `Clone` for non-`Clone` `T`, so we have to spell it out.
fn opt_clone(py: Python<'_>, o: &Option<PyObject>) -> Option<PyObject> {
    o.as_ref().map(|x| x.clone_ref(py))
}

#[pyfunction]
pub fn constraint_location(py: Python<'_>, c: PyObject) -> PyResult<PyObject> {
    let bound = c.bind(py);
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        return Ok(opt_clone(py, &lc.borrow().loc).unwrap_or_else(|| py.None()));
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        if let Some(l) = &imp.loc {
            return Ok(l.clone_ref(py));
        }
        let seq = imp.seq.clone_ref(py);
        drop(imp);
        return constraint_location(py, seq);
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        if let Some(l) = &conj.loc {
            return Ok(l.clone_ref(py));
        }
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        drop(conj);
        let l1 = constraint_location(py, c1)?;
        if !l1.is_none(py) {
            return Ok(l1);
        }
        return constraint_location(py, c2);
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let seq = u.borrow().seq.clone_ref(py);
        return constraint_location(py, seq);
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let seq = r.borrow().seq.clone_ref(py);
        return constraint_location(py, seq);
    }
    Ok(py.None())
}

// =============================================================================
// imp / end / conj — small Constraint constructors.
//
// The string overloads stay on the Python side (they depend on the lark
// parser); these versions only accept already-parsed LiquidTerm /
// Constraint instances.
// =============================================================================

#[pyfunction]
pub fn imp(py: Python<'_>, expr: PyObject, b: PyObject) -> PyResult<PyObject> {
    let fresh_id = crate::name::next_fresh_id(py)?;
    let name = Py::new(py, Name { name: "_".to_string(), id: fresh_id })?;
    let t_bool = bool_tc(py)?;
    new_implication(py, name, t_bool, expr, b, None)
}

#[pyfunction]
pub fn end(py: Python<'_>, expr: PyObject) -> PyResult<PyObject> {
    new_liquid_constraint(py, expr, None)
}

#[pyfunction]
pub fn conj(py: Python<'_>, a: PyObject, b: PyObject) -> PyResult<PyObject> {
    new_conjunction(py, a, b, None)
}

// =============================================================================
// constraint_builder — wrap a body in nested binders.
// =============================================================================

#[pyfunction]
pub fn constraint_builder(py: Python<'_>, vs: Py<PyList>, exp: PyObject) -> PyResult<PyObject> {
    let mut current = exp;
    let vs_b = vs.bind(py);
    for i in (0..vs_b.len()).rev() {
        let tup = vs_b.get_item(i)?;
        let n: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
        let t: PyObject = tup.get_item(1)?.unbind();
        let t_bound = t.bind(py);
        if t_bound.is_instance_of::<AbstractionType>() {
            current = new_uninterpreted_function_declaration(py, n, t, current)?;
        } else {
            let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
            current = new_implication(py, n, t, lb, current, None)?;
        }
    }
    Ok(current)
}

// =============================================================================
// simplify_expr / simplify_is_true / flatten_conjunctions
// =============================================================================

fn is_liquid_lit_bool(py: Python<'_>, t: &PyObject, val: bool) -> bool {
    if let Ok(b) = t.bind(py).downcast::<LiquidLiteralBool>() {
        b.borrow().value == val
    } else {
        false
    }
}

fn liquid_term_eq(py: Python<'_>, a: &PyObject, b: &PyObject) -> PyResult<bool> {
    a.bind(py).eq(b.bind(py))
}

fn name_is(py: Python<'_>, n: &Py<Name>, expected: &str, expected_id: i64) -> bool {
    let n = n.borrow(py);
    n.name == expected && n.id == expected_id
}

#[pyfunction]
pub fn simplify_expr(py: Python<'_>, expr: PyObject) -> PyResult<PyObject> {
    let bound = expr.bind(py);
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let loc = app.loc.clone_ref(py);
        // Recursively simplify args.
        let args_b = app.args.bind(py);
        let mut sargs: Vec<PyObject> = Vec::with_capacity(args_b.len());
        for i in 0..args_b.len() {
            let a = args_b.get_item(i)?.unbind();
            sargs.push(simplify_expr(py, a)?);
        }
        drop(app);

        if name_is(py, &fun, "&&", 0) && sargs.len() == 2 {
            if is_liquid_lit_bool(py, &sargs[0], false) || is_liquid_lit_bool(py, &sargs[1], false) {
                return new_liquid_literal_bool(py, false, loc);
            }
            if is_liquid_lit_bool(py, &sargs[0], true) {
                return Ok(sargs.swap_remove(1));
            }
            if is_liquid_lit_bool(py, &sargs[1], true) {
                return Ok(sargs.swap_remove(0));
            }
            if liquid_term_eq(py, &sargs[0], &sargs[1])? {
                return Ok(sargs.swap_remove(0));
            }
        }
        if name_is(py, &fun, "||", 0) && sargs.len() == 2 {
            if is_liquid_lit_bool(py, &sargs[0], true) || is_liquid_lit_bool(py, &sargs[1], true) {
                return new_liquid_literal_bool(py, true, loc);
            }
            if is_liquid_lit_bool(py, &sargs[0], false) {
                return Ok(sargs.swap_remove(1));
            }
            if is_liquid_lit_bool(py, &sargs[1], false) {
                return Ok(sargs.swap_remove(0));
            }
            if liquid_term_eq(py, &sargs[0], &sargs[1])? {
                return Ok(sargs.swap_remove(0));
            }
        }
        if name_is(py, &fun, "!", 0) && sargs.len() == 1 {
            if is_liquid_lit_bool(py, &sargs[0], true) {
                return new_liquid_literal_bool(py, false, loc);
            }
            if is_liquid_lit_bool(py, &sargs[0], false) {
                return new_liquid_literal_bool(py, true, loc);
            }
            // !(!x) -> x
            if let Ok(inner) = sargs[0].bind(py).downcast::<LiquidApp>() {
                let inner = inner.borrow();
                if name_is(py, &inner.fun, "!", 0) {
                    let inner_args = inner.args.bind(py);
                    if inner_args.len() == 1 {
                        return Ok(inner_args.get_item(0)?.unbind());
                    }
                }
            }
        }
        if name_is(py, &fun, "==", 0) && sargs.len() == 2 && liquid_term_eq(py, &sargs[0], &sargs[1])? {
            return new_liquid_literal_bool(py, true, loc);
        }
        let new_args = PyList::new_bound(py, &sargs).unbind();
        return new_liquid_app(py, fun, new_args, loc);
    }
    Ok(expr)
}

#[pyfunction]
pub fn simplify_is_true(py: Python<'_>, c: PyObject) -> PyResult<bool> {
    let bound = c.bind(py);
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let lc = lc.borrow();
        return Ok(is_liquid_lit_bool(py, &lc.expr, true));
    }
    Ok(false)
}

#[pyfunction]
pub fn flatten_conjunctions(py: Python<'_>, c: PyObject) -> PyResult<Py<PyList>> {
    // c is expected to be a Conjunction; we flatten its tree.
    let bound = c.bind(py);
    let conj = bound.downcast::<Conjunction>()?.borrow();
    let mut queue: Vec<PyObject> = vec![conj.c1.clone_ref(py), conj.c2.clone_ref(py)];
    drop(conj);

    let out = PyList::empty_bound(py);
    while let Some(o) = queue.pop() {
        if let Ok(c) = o.bind(py).downcast::<Conjunction>() {
            let c = c.borrow();
            queue.push(c.c1.clone_ref(py));
            queue.push(c.c2.clone_ref(py));
            continue;
        }
        if simplify_is_true(py, o.clone_ref(py))? {
            continue;
        }
        out.append(o)?;
    }
    Ok(out.unbind())
}

// =============================================================================
// is_used / is_used_liquid
// =============================================================================

#[pyfunction]
pub fn is_used_liquid(py: Python<'_>, n: Py<Name>, c: PyObject) -> PyResult<bool> {
    let fvs = liquid_free_vars(py, c)?;
    let fvs_b = fvs.bind(py);
    let target = n.borrow(py);
    for i in 0..fvs_b.len() {
        let item = fvs_b.get_item(i)?;
        let nm = item.downcast::<Name>()?.borrow();
        if nm.name == target.name && nm.id == target.id {
            return Ok(true);
        }
    }
    Ok(false)
}

#[pyfunction]
pub fn is_used(py: Python<'_>, n: Py<Name>, c: PyObject) -> PyResult<bool> {
    let bound = c.bind(py);
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let expr = lc.borrow().expr.clone_ref(py);
        return is_used_liquid(py, n, expr);
    }
    if bound.is_instance_of::<UninterpretedFunctionDeclaration>() {
        return Ok(false);
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let body = r.borrow().body.clone_ref(py);
        let seq = r.borrow().seq.clone_ref(py);
        return Ok(is_used_liquid(py, n.clone_ref(py), body)? || is_used(py, n, seq)?);
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let iname = imp.name.borrow(py);
        let target = n.borrow(py);
        if iname.name == target.name && iname.id == target.id {
            return Ok(false);
        }
        drop(iname);
        drop(target);
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        drop(imp);
        return Ok(is_used_liquid(py, n.clone_ref(py), pred)? || is_used(py, n, seq)?);
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        drop(conj);
        return Ok(is_used(py, n.clone_ref(py), c1)? || is_used(py, n, c2)?);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unsupported Constraint: {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// constraint_free_variables
// =============================================================================

#[pyfunction]
pub fn constraint_free_variables(py: Python<'_>, c: PyObject) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    cfv_into(py, c, &out)?;
    Ok(out.unbind())
}

fn cfv_into(py: Python<'_>, c: PyObject, out: &Bound<'_, PyList>) -> PyResult<()> {
    let bound = c.bind(py);
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let expr = lc.borrow().expr.clone_ref(py);
        let fvs = liquid_free_vars(py, expr)?;
        let fvs_b = fvs.bind(py);
        for i in 0..fvs_b.len() {
            out.append(fvs_b.get_item(i)?)?;
        }
        return Ok(());
    }
    if bound.is_instance_of::<UninterpretedFunctionDeclaration>() {
        return Ok(());
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let r = r.borrow();
        let body = r.body.clone_ref(py);
        let params = r.params.clone_ref(py);
        let seq = r.seq.clone_ref(py);
        drop(r);
        let body_fvs = liquid_free_vars(py, body)?;
        let body_b = body_fvs.bind(py);
        let params_b = params.bind(py);
        // Filter out variables bound by params.
        for i in 0..body_b.len() {
            let v = body_b.get_item(i)?;
            let v_name = v.downcast::<Name>()?.borrow();
            let mut bound_here = false;
            for j in 0..params_b.len() {
                let p = params_b.get_item(j)?;
                let p_name = p.downcast::<Name>()?.borrow();
                if p_name.name == v_name.name && p_name.id == v_name.id {
                    bound_here = true;
                    break;
                }
            }
            if !bound_here {
                out.append(v.clone())?;
            }
        }
        return cfv_into(py, seq, out);
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        let iname = imp.name.clone_ref(py);
        drop(imp);
        let lv = liquid_free_vars(py, pred)?;
        let lv_b = lv.bind(py);
        let iname_b = iname.borrow(py);
        for i in 0..lv_b.len() {
            let v = lv_b.get_item(i)?;
            let n = v.downcast::<Name>()?.borrow();
            if !(n.name == iname_b.name && n.id == iname_b.id) {
                out.append(v.clone())?;
            }
        }
        drop(iname_b);
        // Recurse into seq, filtering iname.
        let tmp = PyList::empty_bound(py);
        cfv_into(py, seq, &tmp)?;
        let iname_b = iname.borrow(py);
        for i in 0..tmp.len() {
            let v = tmp.get_item(i)?;
            let n = v.downcast::<Name>()?.borrow();
            if !(n.name == iname_b.name && n.id == iname_b.id) {
                out.append(v.clone())?;
            }
        }
        return Ok(());
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        drop(conj);
        cfv_into(py, c1, out)?;
        return cfv_into(py, c2, out);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unsupported Constraint: {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// substitution_in_constraint
// =============================================================================

#[pyfunction]
pub fn substitution_in_constraint(
    py: Python<'_>,
    c: PyObject,
    rep: PyObject,
    name: Py<Name>,
) -> PyResult<PyObject> {
    let bound = c.bind(py);

    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let lc = lc.borrow();
        let expr = lc.expr.clone_ref(py);
        let loc = opt_clone(py, &lc.loc);
        drop(lc);
        let new_expr = substitution_in_liquid(py, expr, rep, name)?;
        return new_liquid_constraint(py, new_expr, loc);
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        let loc = opt_clone(py, &conj.loc);
        drop(conj);
        let left = substitution_in_constraint(py, c1, rep.clone_ref(py), name.clone_ref(py))?;
        let right = substitution_in_constraint(py, c2, rep, name)?;
        return new_conjunction(py, left, right, loc);
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let impl_name = imp.name.clone_ref(py);
        let base = imp.base.clone_ref(py);
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        let loc = opt_clone(py, &imp.loc);
        drop(imp);

        let impl_n = impl_name.borrow(py);
        let target_n = name.borrow(py);
        if impl_n.name == target_n.name && impl_n.id == target_n.id {
            drop(impl_n);
            drop(target_n);
            return Ok(c);
        }
        drop(impl_n);
        drop(target_n);
        let nseq = substitution_in_constraint(py, seq, rep.clone_ref(py), name.clone_ref(py))?;
        let new_pred = substitution_in_liquid(py, pred, rep, name)?;
        return new_implication(py, impl_name, base, new_pred, nseq, loc);
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let u = u.borrow();
        let uname = u.name.clone_ref(py);
        let utype = u.type_.clone_ref(py);
        let seq = u.seq.clone_ref(py);
        drop(u);
        let nseq = substitution_in_constraint(py, seq, rep, name)?;
        return new_uninterpreted_function_declaration(py, uname, utype, nseq);
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let r = r.borrow();
        let rname = r.name.clone_ref(py);
        let rtype = r.type_.clone_ref(py);
        let params = r.params.clone_ref(py);
        let body = r.body.clone_ref(py);
        let seq = r.seq.clone_ref(py);
        drop(r);
        let nbody = substitution_in_liquid(py, body, rep.clone_ref(py), name.clone_ref(py))?;
        let nseq = substitution_in_constraint(py, seq, rep, name)?;
        return new_reflected_function_declaration(py, rname, rtype, params, nbody, nseq);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "substitution_in_constraint: unsupported {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// used_variables — names used in a LiquidTerm that aren't built-in operators.
// =============================================================================

fn is_builtin_op(name: &str) -> bool {
    matches!(
        name,
        "==" | "!=" | "<" | "<=" | ">" | ">=" | "!" | "&&" | "||" | "+" | "-" | "*" | "/"
            | "%" | "-->" | "Set_empty" | "Set_sng" | "Set_cup" | "Set_cap" | "Set_dif"
            | "Set_mem" | "Set_sub"
    )
}

#[pyfunction]
pub fn used_variables(py: Python<'_>, c: PyObject) -> PyResult<Py<pyo3::types::PySet>> {
    let fvs = liquid_free_vars(py, c)?;
    let out = pyo3::types::PySet::empty_bound(py)?;
    let fvs_b = fvs.bind(py);
    for i in 0..fvs_b.len() {
        let v = fvs_b.get_item(i)?;
        let n = v.downcast::<Name>()?.borrow();
        if !is_builtin_op(&n.name) {
            drop(n);
            out.add(v)?;
        }
    }
    Ok(out.unbind())
}

// =============================================================================
// simplify_constraint
// =============================================================================

fn is_synthesized_name(py: Python<'_>, n: &Py<Name>) -> bool {
    n.borrow(py).name == "_y"
}

#[pyfunction]
pub fn simplify_constraint(py: Python<'_>, c: PyObject) -> PyResult<PyObject> {
    let bound = c.bind(py);

    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let expr = lc.borrow().expr.clone_ref(py);
        let s = simplify_expr(py, expr)?;
        return new_liquid_constraint(py, s, None);
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        drop(conj);
        let left = simplify_constraint(py, c1)?;
        let right = simplify_constraint(py, c2)?;
        if left.bind(py).eq(right.bind(py))? {
            return Ok(left);
        }
        if let Ok(lc) = left.bind(py).downcast::<LiquidConstraint>() {
            if is_liquid_lit_bool(py, &lc.borrow().expr, false) {
                return Ok(left);
            }
        }
        if let Ok(rc) = right.bind(py).downcast::<LiquidConstraint>() {
            if is_liquid_lit_bool(py, &rc.borrow().expr, false) {
                return Ok(right);
            }
        }
        if let Ok(lc) = left.bind(py).downcast::<LiquidConstraint>() {
            if is_liquid_lit_bool(py, &lc.borrow().expr, true) {
                return Ok(right);
            }
        }
        if let Ok(rc) = right.bind(py).downcast::<LiquidConstraint>() {
            if is_liquid_lit_bool(py, &rc.borrow().expr, true) {
                return Ok(left);
            }
        }
        return new_conjunction(py, left, right, None);
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let iname = imp.name.clone_ref(py);
        let base = imp.base.clone_ref(py);
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        let iloc = opt_clone(py, &imp.loc);
        drop(imp);

        // pred == true  and  seq == true  →  seq
        if is_liquid_lit_bool(py, &pred, true) {
            if let Ok(lc) = seq.bind(py).downcast::<LiquidConstraint>() {
                if is_liquid_lit_bool(py, &lc.borrow().expr, true) {
                    return Ok(seq);
                }
            }
        }

        // Synthesised "_y" binder with an equality refinement: substitute it
        // away to keep the SMT query small.
        if is_synthesized_name(py, &iname) {
            if let Ok(app) = pred.bind(py).downcast::<LiquidApp>() {
                let app = app.borrow();
                if name_is(py, &app.fun, "==", 0) {
                    let args = app.args.bind(py);
                    if args.len() == 2 {
                        let a0 = args.get_item(0)?.unbind();
                        let a1 = args.get_item(1)?.unbind();
                        // pred is (iname == rep) ?
                        let rep: Option<PyObject> = if is_liquid_var_eq(py, &a0, &iname)? {
                            Some(a1.clone_ref(py))
                        } else if is_liquid_var_eq(py, &a1, &iname)? {
                            Some(a0.clone_ref(py))
                        } else {
                            None
                        };
                        if let Some(rep) = rep {
                            drop(app);
                            let subs_seq = substitution_in_constraint(py, seq, rep, iname)?;
                            return simplify_constraint(py, subs_seq);
                        }
                    }
                }
            }
        }

        // pred = (cond) && (iname == rep)  pattern.
        if let Ok(app) = pred.bind(py).downcast::<LiquidApp>() {
            let app = app.borrow();
            if name_is(py, &app.fun, "&&", 0) {
                let args = app.args.bind(py);
                if args.len() == 2 {
                    let a1 = args.get_item(1)?;
                    if let Ok(inner) = a1.downcast::<LiquidApp>() {
                        let inner_b = inner.borrow();
                        if name_is(py, &inner_b.fun, "==", 0) {
                            let inner_args = inner_b.args.bind(py);
                            if inner_args.len() == 2 {
                                let ia0 = inner_args.get_item(0)?.unbind();
                                if is_liquid_var_eq(py, &ia0, &iname)? {
                                    let ia1 = inner_args.get_item(1)?.unbind();
                                    let cond = args.get_item(0)?.unbind();
                                    drop(inner_b);
                                    drop(app);
                                    let subs_pred = substitution_in_liquid(
                                        py,
                                        cond,
                                        ia1.clone_ref(py),
                                        iname.clone_ref(py),
                                    )?;
                                    let subs_seq = substitution_in_constraint(
                                        py,
                                        seq,
                                        ia1,
                                        iname.clone_ref(py),
                                    )?;
                                    let fresh_id = crate::name::next_fresh_id(py)?;
                                    let new_n =
                                        Py::new(py, Name { name: "_".to_string(), id: fresh_id })?;
                                    let t_bool = bool_tc(py)?;
                                    let inner_imp = new_implication(
                                        py, new_n, t_bool, subs_pred, subs_seq, iloc,
                                    )?;
                                    return simplify_constraint(py, inner_imp);
                                }
                            }
                        }
                    }
                }
            }
        }

        let cont = simplify_constraint(py, seq)?;
        let s = simplify_expr(py, pred)?;

        // Drop binders that aren't used anywhere downstream.
        let used = used_variables(py, s.clone_ref(py))?;
        let used_b = used.bind(py);
        let mut other_used = false;
        for item in used_b.iter() {
            let n_obj = item;
            let n_name = n_obj.downcast::<Name>()?.borrow();
            let iname_b = iname.borrow(py);
            if !(n_name.name == iname_b.name && n_name.id == iname_b.id) {
                other_used = true;
                break;
            }
        }
        let cont_uses = is_used(py, iname.clone_ref(py), cont.clone_ref(py))?;
        if !cont_uses && !other_used {
            return Ok(cont);
        }

        return new_implication(py, iname, base, s, cont, iloc);
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let u = u.borrow();
        let uname = u.name.clone_ref(py);
        let utype = u.type_.clone_ref(py);
        let useq = u.seq.clone_ref(py);
        drop(u);
        let cont = simplify_constraint(py, useq)?;
        return new_uninterpreted_function_declaration(py, uname, utype, cont);
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let r = r.borrow();
        let rname = r.name.clone_ref(py);
        let rtype = r.type_.clone_ref(py);
        let rparams = r.params.clone_ref(py);
        let rbody = r.body.clone_ref(py);
        let rseq = r.seq.clone_ref(py);
        drop(r);
        let cont = simplify_constraint(py, rseq)?;
        let nbody = simplify_expr(py, rbody)?;
        return new_reflected_function_declaration(py, rname, rtype, rparams, nbody, cont);
    }
    Ok(c)
}

fn is_liquid_var_eq(py: Python<'_>, t: &PyObject, name: &Py<Name>) -> PyResult<bool> {
    if let Ok(v) = t.bind(py).downcast::<LiquidVar>() {
        let v = v.borrow();
        let vn = v.name.borrow(py);
        let tn = name.borrow(py);
        return Ok(vn.name == tn.name && vn.id == tn.id);
    }
    Ok(false)
}

fn bool_tc(py: Python<'_>) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: "Bool".to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    new_type_constructor(py, n, empty, crate::loc::default_location(py))
}

// =============================================================================
// simplify_constraint_fixpoint
// =============================================================================

#[pyfunction]
#[pyo3(signature = (c, max_steps = 16))]
pub fn simplify_constraint_fixpoint(
    py: Python<'_>,
    c: PyObject,
    max_steps: usize,
) -> PyResult<PyObject> {
    let mut cur = c;
    for _ in 0..max_steps {
        let nxt = simplify_constraint(py, cur.clone_ref(py))?;
        if cur.bind(py).eq(nxt.bind(py))? {
            return Ok(cur);
        }
        cur = nxt;
    }
    Ok(cur)
}

// =============================================================================
// conjunctive_normal_form — materialised list (Python uses a generator).
// =============================================================================

#[pyfunction]
pub fn conjunctive_normal_form(py: Python<'_>, c: PyObject) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    cnf_into(py, c, &out)?;
    Ok(out.unbind())
}

fn cnf_into(py: Python<'_>, c: PyObject, out: &Bound<'_, PyList>) -> PyResult<()> {
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
        cnf_into(py, c1, out)?;
        return cnf_into(py, c2, out);
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let iname = imp.name.clone_ref(py);
        let base = imp.base.clone_ref(py);
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        let iloc = opt_clone(py, &imp.loc);
        drop(imp);
        let inner = PyList::empty_bound(py);
        cnf_into(py, seq, &inner)?;
        for i in 0..inner.len() {
            let item = inner.get_item(i)?.unbind();
            let wrapped = new_implication(
                py,
                iname.clone_ref(py),
                base.clone_ref(py),
                pred.clone_ref(py),
                item,
                opt_clone(py, &iloc),
            )?;
            out.append(wrapped)?;
        }
        return Ok(());
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let u = u.borrow();
        let uname = u.name.clone_ref(py);
        let utype = u.type_.clone_ref(py);
        let useq = u.seq.clone_ref(py);
        drop(u);
        let inner = PyList::empty_bound(py);
        cnf_into(py, useq, &inner)?;
        for i in 0..inner.len() {
            let item = inner.get_item(i)?.unbind();
            out.append(new_uninterpreted_function_declaration(
                py,
                uname.clone_ref(py),
                utype.clone_ref(py),
                item,
            )?)?;
        }
        return Ok(());
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let r = r.borrow();
        let rname = r.name.clone_ref(py);
        let rtype = r.type_.clone_ref(py);
        let rparams = r.params.clone_ref(py);
        let rbody = r.body.clone_ref(py);
        let rseq = r.seq.clone_ref(py);
        drop(r);
        let inner = PyList::empty_bound(py);
        cnf_into(py, rseq, &inner)?;
        for i in 0..inner.len() {
            let item = inner.get_item(i)?.unbind();
            out.append(new_reflected_function_declaration(
                py,
                rname.clone_ref(py),
                rtype.clone_ref(py),
                rparams.clone_ref(py),
                rbody.clone_ref(py),
                item,
            )?)?;
        }
        return Ok(());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "conjunctive_normal_form: unsupported {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// split_or_disjuncts / split_or_in_conclusion
// =============================================================================

#[pyfunction]
pub fn split_or_disjuncts(py: Python<'_>, expr: PyObject) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    sod_into(py, expr, &out)?;
    Ok(out.unbind())
}

fn sod_into(py: Python<'_>, expr: PyObject, out: &Bound<'_, PyList>) -> PyResult<()> {
    if let Ok(app) = expr.bind(py).downcast::<LiquidApp>() {
        let app = app.borrow();
        if name_is(py, &app.fun, "||", 0) {
            let args = app.args.bind(py);
            if args.len() == 2 {
                let a0 = args.get_item(0)?.unbind();
                let a1 = args.get_item(1)?.unbind();
                drop(app);
                sod_into(py, a0, out)?;
                return sod_into(py, a1, out);
            }
        }
    }
    let lc = new_liquid_constraint(py, expr, None)?;
    out.append(lc)?;
    Ok(())
}

#[pyfunction]
pub fn split_or_in_conclusion(py: Python<'_>, c: PyObject) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    soc_into(py, c, &out)?;
    Ok(out.unbind())
}

fn soc_into(py: Python<'_>, c: PyObject, out: &Bound<'_, PyList>) -> PyResult<()> {
    let bound = c.bind(py);
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let expr = lc.borrow().expr.clone_ref(py);
        let pieces = split_or_disjuncts(py, expr)?;
        let p_b = pieces.bind(py);
        for i in 0..p_b.len() {
            out.append(p_b.get_item(i)?)?;
        }
        return Ok(());
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let iname = imp.name.clone_ref(py);
        let base = imp.base.clone_ref(py);
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        let iloc = opt_clone(py, &imp.loc);
        drop(imp);
        let inner = PyList::empty_bound(py);
        soc_into(py, seq, &inner)?;
        for i in 0..inner.len() {
            let item = inner.get_item(i)?.unbind();
            out.append(new_implication(
                py,
                iname.clone_ref(py),
                base.clone_ref(py),
                pred.clone_ref(py),
                item,
                opt_clone(py, &iloc),
            )?)?;
        }
        return Ok(());
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let u = u.borrow();
        let uname = u.name.clone_ref(py);
        let utype = u.type_.clone_ref(py);
        let useq = u.seq.clone_ref(py);
        drop(u);
        let inner = PyList::empty_bound(py);
        soc_into(py, useq, &inner)?;
        for i in 0..inner.len() {
            let item = inner.get_item(i)?.unbind();
            out.append(new_uninterpreted_function_declaration(
                py,
                uname.clone_ref(py),
                utype.clone_ref(py),
                item,
            )?)?;
        }
        return Ok(());
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let r = r.borrow();
        let rname = r.name.clone_ref(py);
        let rtype = r.type_.clone_ref(py);
        let rparams = r.params.clone_ref(py);
        let rbody = r.body.clone_ref(py);
        let rseq = r.seq.clone_ref(py);
        drop(r);
        let inner = PyList::empty_bound(py);
        soc_into(py, rseq, &inner)?;
        for i in 0..inner.len() {
            let item = inner.get_item(i)?.unbind();
            out.append(new_reflected_function_declaration(
                py,
                rname.clone_ref(py),
                rtype.clone_ref(py),
                rparams.clone_ref(py),
                rbody.clone_ref(py),
                item,
            )?)?;
        }
        return Ok(());
    }
    // Fallthrough: just push the constraint itself.
    out.append(c)?;
    Ok(())
}

// =============================================================================
// is_implication_true
// =============================================================================

#[pyfunction]
pub fn is_implication_true(py: Python<'_>, c: PyObject) -> PyResult<bool> {
    let bound = c.bind(py);
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        return Ok(is_liquid_lit_bool(py, &lc.borrow().expr, true));
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let seq = u.borrow().seq.clone_ref(py);
        return is_implication_true(py, seq);
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let seq = r.borrow().seq.clone_ref(py);
        return is_implication_true(py, seq);
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let seq = imp.borrow().seq.clone_ref(py);
        return is_implication_true(py, seq);
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        drop(conj);
        return Ok(is_implication_true(py, c1)? && is_implication_true(py, c2)?);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "is_implication_true: unsupported {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// remove_unrelated_context
// =============================================================================

#[pyfunction]
pub fn remove_unrelated_context(
    py: Python<'_>,
    c: PyObject,
    ignore_vars: Py<pyo3::types::PySet>,
) -> PyResult<Py<pyo3::types::PyTuple>> {
    let (new_c, vars) = rur_inner(py, c, ignore_vars)?;
    let vars_set = pyo3::types::PySet::empty_bound(py)?;
    for (_, name_obj) in vars {
        vars_set.add(name_obj)?;
    }
    Ok(pyo3::types::PyTuple::new_bound(py, &[new_c, vars_set.unbind().into_any()]).unbind())
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct NameKey {
    name: String,
    id: i64,
}

fn name_to_key(py: Python<'_>, n: &Py<Name>) -> NameKey {
    let n = n.borrow(py);
    NameKey { name: n.name.clone(), id: n.id }
}

/// Var collection: a NameKey-indexed map keeping one canonical `Py<Name>`
/// for every distinct variable. Equality / membership go through NameKey;
/// the Py<Name> is preserved so the caller can rebuild a PySet of names.
type VarMap = std::collections::HashMap<NameKey, Py<Name>>;

fn pyset_to_keys(
    py: Python<'_>,
    s: &Py<pyo3::types::PySet>,
) -> PyResult<HashSet<NameKey>> {
    let mut out = HashSet::new();
    for item in s.bind(py).iter() {
        if let Ok(n) = item.downcast::<Name>() {
            let n = n.borrow();
            out.insert(NameKey { name: n.name.clone(), id: n.id });
        }
    }
    Ok(out)
}

fn rur_inner(
    py: Python<'_>,
    c: PyObject,
    ignore_vars: Py<pyo3::types::PySet>,
) -> PyResult<(PyObject, VarMap)> {
    let bound = c.bind(py);
    let ignore_set = pyset_to_keys(py, &ignore_vars)?;

    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let expr = lc.borrow().expr.clone_ref(py);
        let used = used_variables(py, expr)?;
        let mut vs: VarMap = std::collections::HashMap::new();
        for item in used.bind(py).iter() {
            let n_obj = item.downcast::<Name>()?.clone();
            let n = n_obj.borrow();
            let key = NameKey { name: n.name.clone(), id: n.id };
            drop(n);
            if !ignore_set.contains(&key) {
                vs.entry(key).or_insert_with(|| n_obj.unbind());
            }
        }
        return Ok((c, vs));
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let u = u.borrow();
        let uname = u.name.clone_ref(py);
        let useq = u.seq.clone_ref(py);
        drop(u);
        let new_ignore = pyo3::types::PySet::empty_bound(py)?;
        for item in ignore_vars.bind(py).iter() {
            new_ignore.add(item)?;
        }
        new_ignore.add(uname)?;
        return rur_inner(py, useq, new_ignore.unbind());
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let r = r.borrow();
        let rname = r.name.clone_ref(py);
        let rseq = r.seq.clone_ref(py);
        drop(r);
        let new_ignore = pyo3::types::PySet::empty_bound(py)?;
        for item in ignore_vars.bind(py).iter() {
            new_ignore.add(item)?;
        }
        new_ignore.add(rname)?;
        return rur_inner(py, rseq, new_ignore.unbind());
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let iname = imp.name.clone_ref(py);
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        drop(imp);
        let (ic, vs) = rur_inner(py, seq, ignore_vars.clone_ref(py))?;

        let used = used_variables(py, pred)?;
        let mut current_vars: VarMap = std::collections::HashMap::new();
        for item in used.bind(py).iter() {
            let n_obj = item.downcast::<Name>()?.clone();
            let n = n_obj.borrow();
            let key = NameKey { name: n.name.clone(), id: n.id };
            drop(n);
            if !ignore_set.contains(&key) {
                current_vars.entry(key).or_insert_with(|| n_obj.unbind());
            }
        }
        let iname_key = name_to_key(py, &iname);
        current_vars.entry(iname_key.clone()).or_insert(iname);

        let is_disjoint = !vs.keys().any(|k| current_vars.contains_key(k));
        if is_disjoint {
            return Ok((ic, vs));
        }
        let mut merged = vs;
        for (k, v) in current_vars {
            merged.entry(k).or_insert(v);
        }
        merged.remove(&iname_key);
        return Ok((c, merged));
    }
    if let Ok(conj) = bound.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let c1 = conj.c1.clone_ref(py);
        let c2 = conj.c2.clone_ref(py);
        let cloc = opt_clone(py, &conj.loc);
        drop(conj);
        let (p1, vs1) = rur_inner(py, c1, ignore_vars.clone_ref(py))?;
        let (p2, vs2) = rur_inner(py, c2, ignore_vars)?;
        let new_c = new_conjunction(py, p1, p2, cloc)?;
        let mut merged = vs1;
        for (k, v) in vs2 {
            merged.entry(k).or_insert(v);
        }
        return Ok((new_c, merged));
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "remove_unrelated_context: unsupported {}",
        bound.repr()?.to_string()
    )))
}

// =============================================================================
// reduce_to_useful_constraint
// =============================================================================

#[pyfunction]
pub fn reduce_to_useful_constraint(py: Python<'_>, c: PyObject) -> PyResult<PyObject> {
    let cnf = conjunctive_normal_form(py, c)?;
    let cnf_b = cnf.bind(py);
    let mut top: Vec<PyObject> = Vec::new();
    let empty_set = pyo3::types::PySet::empty_bound(py)?.unbind();
    for i in 0..cnf_b.len() {
        let cons = cnf_b.get_item(i)?.unbind();
        if !is_implication_true(py, cons.clone_ref(py))? {
            let cons_simp = simplify_constraint(py, cons)?;
            let tup = remove_unrelated_context(py, cons_simp, empty_set.clone_ref(py))?;
            let cleaned: PyObject = tup.bind(py).get_item(0)?.unbind();
            top.push(cleaned);
        }
    }
    let llb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
    let mut acc: PyObject = new_liquid_constraint(py, llb, None)?;
    for item in top {
        acc = new_conjunction(py, acc, item, None)?;
    }
    Ok(acc)
}

// =============================================================================
// pretty_print_generator / pretty_print_constraint
// =============================================================================

fn pretty_emit(
    py: Python<'_>,
    c: PyObject,
    out: &mut Vec<(String, usize)>,
) -> PyResult<()> {
    let bound = c.bind(py);
    if let Ok(lc) = bound.downcast::<LiquidConstraint>() {
        let expr = lc.borrow().expr.bind(py).str()?.to_string();
        out.push((expr, 0));
        return Ok(());
    }
    if let Ok(u) = bound.downcast::<UninterpretedFunctionDeclaration>() {
        let u = u.borrow();
        let uname = u.name.bind(py).str()?.to_string();
        let utype = u.type_.bind(py).str()?.to_string();
        let useq = u.seq.clone_ref(py);
        drop(u);
        out.push((format!("fun {} : {}", uname, utype), 0));
        return pretty_emit(py, useq, out);
    }
    if let Ok(r) = bound.downcast::<ReflectedFunctionDeclaration>() {
        let r = r.borrow();
        let rname = r.name.bind(py).str()?.to_string();
        let rtype = r.type_.bind(py).str()?.to_string();
        let params_b = r.params.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(params_b.len());
        for i in 0..params_b.len() {
            parts.push(params_b.get_item(i)?.str()?.to_string());
        }
        let rseq = r.seq.clone_ref(py);
        drop(r);
        out.push((
            format!("reflected {}({}) : {}", rname, parts.join(", "), rtype),
            0,
        ));
        return pretty_emit(py, rseq, out);
    }
    if let Ok(imp) = bound.downcast::<Implication>() {
        let imp = imp.borrow();
        let iname = imp.name.bind(py).str()?.to_string();
        let base = imp.base.bind(py).str()?.to_string();
        let pred = imp.pred.clone_ref(py);
        let seq = imp.seq.clone_ref(py);
        let iname_n = imp.name.clone_ref(py);
        drop(imp);

        let pred_str = pred.bind(py).str()?.to_string();
        if is_used(py, iname_n, seq.clone_ref(py))? {
            out.push((format!("∀{}:{} | {}", iname, base, pred_str), 0));
        } else if !is_liquid_lit_bool(py, &pred, true) {
            out.push((format!("{}:_ | {}", iname, pred_str), 0));
        }
        if !seq.bind(py).is_instance_of::<Implication>() {
            out.push(("====>".to_string(), 0));
        }
        return pretty_emit(py, seq, out);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "pretty_print_generator: unsupported {}",
        bound.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn pretty_print_constraint(py: Python<'_>, c: PyObject) -> PyResult<String> {
    let mut blocks: Vec<String> = Vec::new();
    let cnf = conjunctive_normal_form(py, c)?;
    let cnf_b = cnf.bind(py);
    let empty_set = pyo3::types::PySet::empty_bound(py)?.unbind();
    for i in 0..cnf_b.len() {
        let cons = cnf_b.get_item(i)?.unbind();
        if !is_implication_true(py, cons.clone_ref(py))? {
            let cons_simp = simplify_constraint(py, cons)?;
            let tup = remove_unrelated_context(py, cons_simp, empty_set.clone_ref(py))?;
            let cleaned: PyObject = tup.bind(py).get_item(0)?.unbind();
            let mut lines: Vec<(String, usize)> = Vec::new();
            pretty_emit(py, cleaned, &mut lines)?;
            let rendered = lines
                .iter()
                .map(|(s, ind)| format!("{}{}", "\t".repeat(*ind), s))
                .collect::<Vec<_>>()
                .join("\n");
            blocks.push(rendered);
        }
    }
    let header = "\n+-----Constraint-----+\n";
    let middle = blocks.join("\n+--------------------+\n");
    let footer = "\n+---------//---------+\n";
    Ok(format!("{}{}{}", header, middle, footer))
}

#[pyfunction]
pub fn show_constraint(py: Python<'_>, c: PyObject) -> PyResult<()> {
    println!("Could not show constrain:");
    println!("{}", pretty_print_constraint(py, c)?);
    Ok(())
}

#[allow(dead_code)]
fn _silence_unused(
    _t: &LiquidLiteralInt,
    _t2: &LiquidLiteralFloat,
    _t3: &LiquidLiteralString,
    _v: &TypeVar,
    _r: &RefinedType,
    _to: &Top,
    _tc: &TypeConstructor,
) {
}

#[allow(dead_code)]
fn _silence_constraint(_c: &Constraint) {}

#[allow(dead_code)]
fn _silence_refinement_abstraction() {
    let _ = new_refinement_abstraction;
    let _ = new_liquid_var;
}
