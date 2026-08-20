//! Termination metric constraints (port of `aeon.typechecking.termination`).
//!
//! For each recursive call inside a `Rec` with a declared lexicographic
//! metric, generate a Constraint asserting that the metric strictly
//! decreases on every call site.

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::builders::{
    new_application, new_conjunction, new_liquid_app, new_liquid_constraint,
    new_liquid_literal_bool, new_liquid_literal_int, new_var,
};
use crate::liquefy::{inline_lets, liquefy, substitution_in_type};
use crate::liquid::{LiquidApp, LiquidLiteralBool, LiquidVar};
use crate::name::Name;
use crate::smt_ctx::mk_liquid_and;
use crate::substitutions::substitution_in_liquid;
use crate::term_subst::substitution as term_substitution;
use crate::terms::{
    Abstraction, Annotation, Application, If, Let, Rec, RefinementAbstraction,
    RefinementApplication, TypeAbstraction, TypeApplication, Var,
};
use crate::typectx::TypingContext;
use crate::types::{AbstractionType, RefinedType, Type};

/// Clone a `Vec<PyObject>` under the GIL — `PyObject` doesn't implement
/// `Clone`, but `clone_ref` is cheap once we have a `Python<'_>` token.
fn vc(py: Python<'_>, v: &[PyObject]) -> Vec<PyObject> {
    v.iter().map(|o| o.clone_ref(py)).collect()
}

fn ctrue(py: Python<'_>) -> PyResult<PyObject> {
    let lb = new_liquid_literal_bool(py, true, crate::loc::default_location(py))?;
    new_liquid_constraint(py, lb, None)
}

fn cfalse(py: Python<'_>) -> PyResult<PyObject> {
    let lb = new_liquid_literal_bool(py, false, crate::loc::default_location(py))?;
    new_liquid_constraint(py, lb, None)
}

fn mk_liquid_or(py: Python<'_>, a: PyObject, b: PyObject) -> PyResult<PyObject> {
    // Mirror `aeon.core.liquid_ops.mk_liquid_or` short-circuiting.
    let ab = a.bind(py);
    let bb = b.bind(py);
    if let Ok(lb) = ab.downcast::<LiquidLiteralBool>() {
        if lb.borrow().value {
            return Ok(a);
        }
    }
    if let Ok(lb) = bb.downcast::<LiquidLiteralBool>() {
        if lb.borrow().value {
            return Ok(b);
        }
    }
    if let Ok(lb) = ab.downcast::<LiquidLiteralBool>() {
        if !lb.borrow().value {
            return Ok(b);
        }
    }
    if let Ok(lb) = bb.downcast::<LiquidLiteralBool>() {
        if !lb.borrow().value {
            return Ok(a);
        }
    }
    let or_name = Py::new(py, Name { name: "||".to_string(), id: 0 })?;
    let args = PyList::new_bound(py, &[a, b]).unbind();
    new_liquid_app(py, or_name, args, crate::loc::default_location(py))
}

fn name_eq(py: Python<'_>, a: &Py<Name>, b: &Py<Name>) -> bool {
    let a = a.borrow(py);
    let b = b.borrow(py);
    a.name == b.name && a.id == b.id
}

fn peel_abstractions(py: Python<'_>, t: PyObject) -> PyResult<(Vec<Py<Name>>, PyObject)> {
    let mut names: Vec<Py<Name>> = Vec::new();
    let mut cur = t;
    while let Ok(ab) = cur.bind(py).downcast::<Abstraction>() {
        let ab = ab.borrow();
        names.push(ab.var_name.clone_ref(py));
        let body = ab.body.clone_ref(py);
        drop(ab);
        cur = body;
    }
    Ok((names, cur))
}

fn peel_type_formal_names(py: Python<'_>, ty: PyObject) -> PyResult<Vec<Py<Name>>> {
    let mut names: Vec<Py<Name>> = Vec::new();
    let mut cur = ty;
    while let Ok(at) = cur.bind(py).downcast::<AbstractionType>() {
        let at = at.borrow();
        names.push(at.var_name.clone_ref(py));
        let next = at.type_.clone_ref(py);
        drop(at);
        cur = next;
    }
    Ok(names)
}

fn opened_refinement_liquid(
    py: Python<'_>,
    var_type: &PyObject,
    binder_name: &Py<Name>,
    term_formals: &[Py<Name>],
    type_formals: &[Py<Name>],
) -> PyResult<Option<PyObject>> {
    let vb = var_type.bind(py);
    let Ok(rt) = vb.downcast::<RefinedType>() else {
        return Ok(None);
    };
    let rt = rt.borrow();
    let bname = rt.name.clone_ref(py);
    let refinement = rt.refinement.clone_ref(py);
    drop(rt);
    let lv = crate::builders::new_liquid_var(
        py,
        binder_name.clone_ref(py),
        crate::loc::default_location(py),
    )?;
    let opened = substitution_in_liquid(py, refinement, lv, bname)?;
    let aligned = align_liquid_to_type_formals(py, opened, term_formals, type_formals)?;
    Ok(Some(aligned))
}

fn align_liquid_to_type_formals(
    py: Python<'_>,
    liq: PyObject,
    term_names: &[Py<Name>],
    type_names: &[Py<Name>],
) -> PyResult<PyObject> {
    assert_eq!(term_names.len(), type_names.len());
    let mut out = liq;
    for (t_n, ty_n) in term_names.iter().zip(type_names.iter()) {
        if !name_eq(py, t_n, ty_n) {
            let lv = crate::builders::new_liquid_var(
                py,
                ty_n.clone_ref(py),
                crate::loc::default_location(py),
            )?;
            out = substitution_in_liquid(py, out, lv, t_n.clone_ref(py))?;
        }
    }
    Ok(out)
}

fn entry_refinement_liquids(
    py: Python<'_>,
    fn_arrow_type: &PyObject,
    term_formals: &[Py<Name>],
    type_formals: &[Py<Name>],
) -> PyResult<Vec<PyObject>> {
    let mut out: Vec<PyObject> = Vec::new();
    let mut cur = fn_arrow_type.clone_ref(py);
    while let Ok(at) = cur.bind(py).downcast::<AbstractionType>() {
        let at = at.borrow();
        let vname = at.var_name.clone_ref(py);
        let var_type = at.var_type.clone_ref(py);
        let next = at.type_.clone_ref(py);
        drop(at);
        if let Some(liq) =
            opened_refinement_liquid(py, &var_type, &vname, term_formals, type_formals)?
        {
            out.push(liq);
        }
        cur = next;
    }
    Ok(out)
}

fn peel_application_chain(py: Python<'_>, t: PyObject) -> PyResult<(PyObject, Vec<PyObject>)> {
    let mut args: Vec<PyObject> = Vec::new();
    let mut cur = t;
    while let Ok(app) = cur.bind(py).downcast::<Application>() {
        let app = app.borrow();
        args.push(app.arg.clone_ref(py));
        let next = app.fun.clone_ref(py);
        drop(app);
        cur = next;
    }
    args.reverse();
    Ok((cur, args))
}

fn term_bool_not(py: Python<'_>, cond: PyObject) -> PyResult<PyObject> {
    let loc = cond.bind(py).getattr("loc")?.unbind();
    let nname = Py::new(py, Name { name: "!".to_string(), id: 0 })?;
    let var = new_var(py, nname, loc.clone_ref(py))?;
    new_application(py, var, cond, loc)
}

fn synth_type(py: Python<'_>, ctx: PyObject, t: PyObject) -> PyResult<PyObject> {
    // Lazy import — typeinfer imports termination at module load, so we go
    // through Python's import system to break the cycle.
    let res = py
        .import_bound("aeon.typechecking.typeinfer")
        .and_then(|m| m.getattr("synth"))
        .and_then(|f| f.call1((ctx, t)));
    match res {
        Ok(tup) => {
            // synth returns (Constraint, Type); we want the Type.
            tup.get_item(1).map(|x| x.unbind())
        }
        Err(_) => Ok(py.None()),
    }
}

fn substitute_formals(
    py: Python<'_>,
    template: PyObject,
    formals: &[Py<Name>],
    args: &[PyObject],
) -> PyResult<PyObject> {
    assert_eq!(formals.len(), args.len());
    let mut out = template;
    for (formal, arg) in formals.iter().zip(args.iter()) {
        out = term_substitution(py, out, arg.clone_ref(py), formal.clone_ref(py))?;
    }
    Ok(out)
}

fn liquefy_metric_at(
    py: Python<'_>,
    metric: PyObject,
    formals: &[Py<Name>],
    type_formals: &[Py<Name>],
    call_args: Option<&[PyObject]>,
) -> PyResult<Option<PyObject>> {
    let mut t = inline_lets(py, metric)?;
    if let Some(args) = call_args {
        let inlined_args: Vec<PyObject> = args
            .iter()
            .map(|a| inline_lets(py, a.clone_ref(py)))
            .collect::<PyResult<_>>()?;
        t = substitute_formals(py, t, formals, &inlined_args)?;
        t = inline_lets(py, t)?;
    }
    let Some(liq) = liquefy(py, t)? else {
        return Ok(None);
    };
    let aligned = align_liquid_to_type_formals(py, liq, formals, type_formals)?;
    Ok(Some(aligned))
}

fn fold_or(py: Python<'_>, terms: Vec<PyObject>) -> PyResult<PyObject> {
    let mut iter = terms.into_iter();
    let mut acc = iter.next().expect("fold_or: empty");
    for t in iter {
        acc = mk_liquid_or(py, acc, t)?;
    }
    Ok(acc)
}

fn lexicographic_less(
    py: Python<'_>,
    call_ms: &[PyObject],
    entry_ms: &[PyObject],
) -> PyResult<PyObject> {
    assert_eq!(call_ms.len(), entry_ms.len());
    assert!(!call_ms.is_empty());
    let k = call_ms.len();
    let lt_name = Py::new(py, Name { name: "<".to_string(), id: 0 })?;
    let eq_name = Py::new(py, Name { name: "==".to_string(), id: 0 })?;
    let mut disjuncts: Vec<PyObject> = Vec::with_capacity(k);
    for j in 0..k {
        let step_lt_args = PyList::new_bound(py, &[call_ms[j].clone_ref(py), entry_ms[j].clone_ref(py)]).unbind();
        let step_lt = new_liquid_app(py, lt_name.clone_ref(py), step_lt_args, crate::loc::default_location(py))?;
        if j == 0 {
            disjuncts.push(step_lt);
        } else {
            let prefix_args0 = PyList::new_bound(
                py,
                &[call_ms[0].clone_ref(py), entry_ms[0].clone_ref(py)],
            )
            .unbind();
            let mut prefix = new_liquid_app(py, eq_name.clone_ref(py), prefix_args0, crate::loc::default_location(py))?;
            for i in 1..j {
                let prefix_args_i = PyList::new_bound(
                    py,
                    &[call_ms[i].clone_ref(py), entry_ms[i].clone_ref(py)],
                )
                .unbind();
                let eq_step = new_liquid_app(
                    py,
                    eq_name.clone_ref(py),
                    prefix_args_i,
                    crate::loc::default_location(py),
                )?;
                prefix = mk_liquid_and(py, prefix, eq_step)?;
            }
            disjuncts.push(mk_liquid_and(py, prefix, step_lt)?);
        }
    }
    fold_or(py, disjuncts)
}

fn metric_call_non_negative(py: Python<'_>, call_ms: &[PyObject]) -> PyResult<PyObject> {
    let ge_name = Py::new(py, Name { name: ">=".to_string(), id: 0 })?;
    let zero = new_liquid_literal_int(py, 0, crate::loc::default_location(py))?;
    let first_args = PyList::new_bound(py, &[call_ms[0].clone_ref(py), zero.clone_ref(py)]).unbind();
    let mut acc = new_liquid_app(py, ge_name.clone_ref(py), first_args, crate::loc::default_location(py))?;
    for m in call_ms[1..].iter() {
        let nargs = PyList::new_bound(py, &[m.clone_ref(py), zero.clone_ref(py)]).unbind();
        let next = new_liquid_app(py, ge_name.clone_ref(py), nargs, crate::loc::default_location(py))?;
        acc = mk_liquid_and(py, acc, next)?;
    }
    Ok(acc)
}

fn liquefy_path_conjuncts(
    py: Python<'_>,
    path: &[PyObject],
    formals: &[Py<Name>],
    type_formals: &[Py<Name>],
) -> PyResult<Option<PyObject>> {
    if path.is_empty() {
        return Ok(Some(new_liquid_literal_bool(
            py,
            true,
            crate::loc::default_location(py),
        )?));
    }
    let mut parts: Vec<PyObject> = Vec::new();
    for g in path {
        let inlined = inline_lets(py, g.clone_ref(py))?;
        let Some(liq) = liquefy(py, inlined)? else {
            return Ok(None);
        };
        parts.push(align_liquid_to_type_formals(py, liq, formals, type_formals)?);
    }
    let mut iter = parts.into_iter();
    let mut acc = iter.next().unwrap();
    for p in iter {
        acc = mk_liquid_and(py, acc, p)?;
    }
    Ok(Some(acc))
}

fn full_path_guard_liquid(
    py: Python<'_>,
    entry_refs: &[PyObject],
    nested_refs: &[PyObject],
    path: &[PyObject],
    formals: &[Py<Name>],
    type_formals: &[Py<Name>],
) -> PyResult<Option<PyObject>> {
    let mut parts: Vec<PyObject> = Vec::new();
    for r in entry_refs {
        parts.push(r.clone_ref(py));
    }
    for r in nested_refs {
        parts.push(r.clone_ref(py));
    }
    if !path.is_empty() {
        let Some(pl) = liquefy_path_conjuncts(py, path, formals, type_formals)? else {
            return Ok(None);
        };
        let is_lit_true = pl.bind(py).downcast::<LiquidLiteralBool>()
            .map(|b| b.borrow().value).unwrap_or(false);
        if !is_lit_true {
            parts.push(pl);
        }
    }
    if parts.is_empty() {
        return Ok(Some(new_liquid_literal_bool(py, true, crate::loc::default_location(py))?));
    }
    let mut iter = parts.into_iter();
    let mut acc = iter.next().unwrap();
    for p in iter {
        acc = mk_liquid_and(py, acc, p)?;
    }
    Ok(Some(acc))
}

fn termination_obligation(
    py: Python<'_>,
    path: &[PyObject],
    lex: PyObject,
    call_ms: &[PyObject],
    formals: &[Py<Name>],
    type_formals: &[Py<Name>],
    entry_refs: &[PyObject],
    nested_refs: &[PyObject],
) -> PyResult<PyObject> {
    let needs_call_nonneg = !path.is_empty() || !entry_refs.is_empty() || !nested_refs.is_empty();
    let oblig = if needs_call_nonneg {
        let nn = metric_call_non_negative(py, call_ms)?;
        mk_liquid_and(py, lex, nn)?
    } else {
        lex
    };
    let Some(full) = full_path_guard_liquid(py, entry_refs, nested_refs, path, formals, type_formals)? else {
        return cfalse(py);
    };
    let is_true = full.bind(py).downcast::<LiquidLiteralBool>()
        .map(|b| b.borrow().value).unwrap_or(false);
    if is_true {
        return new_liquid_constraint(py, oblig, None);
    }
    let imp_name = Py::new(py, Name { name: "-->".to_string(), id: 0 })?;
    let args = PyList::new_bound(py, &[full, oblig]).unbind();
    let imp_app = new_liquid_app(py, imp_name, args, crate::loc::default_location(py))?;
    new_liquid_constraint(py, imp_app, None)
}

/// (call_args, _loc, path, nested_refs) tuple emitted by the walker.
type CallSite = (Vec<PyObject>, PyObject, Vec<PyObject>, Vec<PyObject>);

fn collect_recursive_calls_with_paths(
    py: Python<'_>,
    fn_name: &Py<Name>,
    arity: usize,
    t: PyObject,
    typing_ctx: Option<PyObject>,
    inner_expect_ty: Option<PyObject>,
    term_formals: &[Py<Name>],
    type_formals: &[Py<Name>],
) -> PyResult<Vec<CallSite>> {
    let mut found: Vec<CallSite> = Vec::new();
    walk_calls(
        py,
        fn_name,
        arity,
        t,
        Vec::new(),
        Vec::new(),
        typing_ctx,
        inner_expect_ty,
        term_formals,
        type_formals,
        &mut found,
    )?;
    Ok(found)
}

#[allow(clippy::too_many_arguments)]
fn walk_calls(
    py: Python<'_>,
    fn_name: &Py<Name>,
    arity: usize,
    tt: PyObject,
    path: Vec<PyObject>,
    nested_refs: Vec<PyObject>,
    ctx: Option<PyObject>,
    expect_ty: Option<PyObject>,
    term_formals: &[Py<Name>],
    type_formals: &[Py<Name>],
    out: &mut Vec<CallSite>,
) -> PyResult<()> {
    let bound = tt.bind(py);

    // Detect a self-application at this node.
    if bound.is_instance_of::<Application>() {
        let (head, args) = peel_application_chain(py, tt.clone_ref(py))?;
        if let Ok(v) = head.bind(py).downcast::<Var>() {
            let v_name = v.borrow().name.clone_ref(py);
            if name_eq(py, &v_name, fn_name) && args.len() == arity {
                let loc = bound.getattr("loc")?.unbind();
                out.push((args, loc, vc(py, &path), vc(py, &nested_refs)));
            }
        }
    }

    // Now recurse into children.
    if let Ok(app) = bound.downcast::<Application>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        drop(app);
        let f_ty = ctx.as_ref().map(|c| synth_type(py, c.clone_ref(py), fun.clone_ref(py))).transpose()?;
        let f_ty_opt = f_ty.and_then(|x| if x.is_none(py) { None } else { Some(x) });
        walk_calls(
            py, fn_name, arity, fun, vc(py, &path), vc(py, &nested_refs), ctx.as_ref().map(|c| c.clone_ref(py)),
            f_ty_opt.as_ref().map(|x| x.clone_ref(py)), term_formals, type_formals, out,
        )?;
        let arg_ty = match f_ty_opt.as_ref() {
            Some(t) => {
                if let Ok(at) = t.bind(py).downcast::<AbstractionType>() {
                    Some(at.borrow().var_type.clone_ref(py))
                } else {
                    None
                }
            }
            None => None,
        };
        walk_calls(
            py, fn_name, arity, arg, path, nested_refs, ctx, arg_ty, term_formals, type_formals, out,
        )?;
        return Ok(());
    }
    if let Ok(ab) = bound.downcast::<Abstraction>() {
        let ab = ab.borrow();
        let name = ab.var_name.clone_ref(py);
        let body = ab.body.clone_ref(py);
        drop(ab);
        if let Some(et) = &expect_ty {
            if let Ok(at) = et.bind(py).downcast::<AbstractionType>() {
                let at = at.borrow();
                let vty = at.var_type.clone_ref(py);
                let next_expect = at.type_.clone_ref(py);
                drop(at);
                let new_ctx = ctx.as_ref().map(|c| -> PyResult<PyObject> {
                    let bound = c.bind(py).downcast::<TypingContext>()?.clone();
                    let new_c = bound.borrow().with_var(py, name.clone_ref(py), vty.clone_ref(py))?;
                    Ok(Py::new(py, new_c)?.into_any())
                }).transpose()?;
                let mut nrefs = vc(py, &nested_refs);
                if let Some(ref_l) = opened_refinement_liquid(py, &vty, &name, term_formals, type_formals)? {
                    nrefs.push(ref_l);
                }
                walk_calls(py, fn_name, arity, body, path, nrefs, new_ctx, Some(next_expect), term_formals, type_formals, out)?;
                return Ok(());
            }
        }
        walk_calls(py, fn_name, arity, body, path, nested_refs, ctx, None, term_formals, type_formals, out)?;
        return Ok(());
    }
    if let Ok(le) = bound.downcast::<Let>() {
        let le = le.borrow();
        let val = le.var_value.clone_ref(py);
        let body = le.body.clone_ref(py);
        drop(le);
        walk_calls(py, fn_name, arity, val, vc(py, &path), vc(py, &nested_refs), ctx.as_ref().map(|c| c.clone_ref(py)), None, term_formals, type_formals, out)?;
        walk_calls(py, fn_name, arity, body, path, nested_refs, ctx, None, term_formals, type_formals, out)?;
        return Ok(());
    }
    if let Ok(rc) = bound.downcast::<Rec>() {
        let rc = rc.borrow();
        let val = rc.var_value.clone_ref(py);
        let body = rc.body.clone_ref(py);
        drop(rc);
        walk_calls(py, fn_name, arity, val, vc(py, &path), vc(py, &nested_refs), ctx.as_ref().map(|c| c.clone_ref(py)), None, term_formals, type_formals, out)?;
        walk_calls(py, fn_name, arity, body, path, nested_refs, ctx, None, term_formals, type_formals, out)?;
        return Ok(());
    }
    if let Ok(an) = bound.downcast::<Annotation>() {
        let expr = an.borrow().expr.clone_ref(py);
        return walk_calls(py, fn_name, arity, expr, path, nested_refs, ctx, expect_ty, term_formals, type_formals, out);
    }
    if let Ok(ife) = bound.downcast::<If>() {
        let ife = ife.borrow();
        let cond = ife.cond.clone_ref(py);
        let then = ife.then.clone_ref(py);
        let otherwise = ife.otherwise.clone_ref(py);
        drop(ife);
        walk_calls(py, fn_name, arity, cond.clone_ref(py), vc(py, &path), vc(py, &nested_refs), ctx.as_ref().map(|c| c.clone_ref(py)), None, term_formals, type_formals, out)?;
        let mut path_t = vc(py, &path);
        path_t.push(cond.clone_ref(py));
        walk_calls(py, fn_name, arity, then, path_t, vc(py, &nested_refs), ctx.as_ref().map(|c| c.clone_ref(py)), expect_ty.as_ref().map(|x| x.clone_ref(py)), term_formals, type_formals, out)?;
        let mut path_e = path;
        let not_cond = term_bool_not(py, cond)?;
        path_e.push(not_cond);
        walk_calls(py, fn_name, arity, otherwise, path_e, nested_refs, ctx, expect_ty, term_formals, type_formals, out)?;
        return Ok(());
    }
    if let Ok(tap) = bound.downcast::<TypeApplication>() {
        let body = tap.borrow().body.clone_ref(py);
        return walk_calls(py, fn_name, arity, body, path, nested_refs, ctx, expect_ty, term_formals, type_formals, out);
    }
    if let Ok(ta) = bound.downcast::<TypeAbstraction>() {
        let body = ta.borrow().body.clone_ref(py);
        return walk_calls(py, fn_name, arity, body, path, nested_refs, ctx, expect_ty, term_formals, type_formals, out);
    }
    if let Ok(rapp) = bound.downcast::<RefinementApplication>() {
        let rapp = rapp.borrow();
        let body = rapp.body.clone_ref(py);
        let refinement = rapp.refinement.clone_ref(py);
        drop(rapp);
        walk_calls(py, fn_name, arity, body, vc(py, &path), vc(py, &nested_refs), ctx.as_ref().map(|c| c.clone_ref(py)), expect_ty, term_formals, type_formals, out)?;
        walk_calls(py, fn_name, arity, refinement, path, nested_refs, ctx, None, term_formals, type_formals, out)?;
        return Ok(());
    }
    if let Ok(rab) = bound.downcast::<RefinementAbstraction>() {
        let body = rab.borrow().body.clone_ref(py);
        return walk_calls(py, fn_name, arity, body, path, nested_refs, ctx, expect_ty, term_formals, type_formals, out);
    }
    Ok(())
}

fn inner_ctx_and_expect_ty(
    py: Python<'_>,
    nrctx: &Py<TypingContext>,
    var_type: PyObject,
    formals: &[Py<Name>],
) -> PyResult<(Py<TypingContext>, PyObject)> {
    let mut ctx = Py::new(
        py,
        TypingContext {
            entries: nrctx.borrow(py).entries.clone_ref(py),
        },
    )?;
    let mut cur_ty = var_type;
    for nm in formals {
        let at = cur_ty.bind(py).downcast::<AbstractionType>()?.clone();
        let at_b = at.borrow();
        let vty = at_b.var_type.clone_ref(py);
        let next = at_b.type_.clone_ref(py);
        drop(at_b);
        let new_ctx = ctx.borrow(py).with_var(py, nm.clone_ref(py), vty)?;
        ctx = Py::new(py, new_ctx)?;
        cur_ty = next;
    }
    Ok((ctx, cur_ty))
}

#[pyfunction]
#[pyo3(signature = (rec, typing_ctx = None))]
pub fn termination_metric_constraints(
    py: Python<'_>,
    rec: &Bound<'_, Rec>,
    typing_ctx: Option<PyObject>,
) -> PyResult<PyObject> {
    let rec_b = rec.borrow();
    let decreasing_by = rec_b.decreasing_by.clone_ref(py);
    let var_name = rec_b.var_name.clone_ref(py);
    let var_type = rec_b.var_type.clone_ref(py);
    let var_value = rec_b.var_value.clone_ref(py);
    drop(rec_b);

    let metrics_b = decreasing_by.bind(py);
    if metrics_b.len() == 0 {
        return ctrue(py);
    }
    let metrics: Vec<PyObject> = (0..metrics_b.len())
        .map(|i| metrics_b.get_item(i).map(|x| x.unbind()))
        .collect::<PyResult<_>>()?;

    let (formals, inner) = peel_abstractions(py, var_value)?;
    let type_formals = peel_type_formal_names(py, var_type.clone_ref(py))?;
    if type_formals.len() != formals.len() {
        return cfalse(py);
    }
    let entry_refs = entry_refinement_liquids(py, &var_type, &formals, &type_formals)?;
    let inner = inline_lets(py, inner)?;
    let arity = formals.len();

    let (inner_ctx_opt, inner_expect_opt) = if let Some(t) = typing_ctx.as_ref() {
        let bound = t.bind(py).downcast::<TypingContext>()?.clone();
        let bound_py: Py<TypingContext> = bound.unbind();
        let (c, e) = inner_ctx_and_expect_ty(py, &bound_py, var_type.clone_ref(py), &formals)?;
        let c_obj: PyObject = c.into_any();
        (Some(c_obj), Some(e))
    } else {
        (None, None)
    };

    let calls = collect_recursive_calls_with_paths(
        py,
        &var_name,
        arity,
        inner,
        inner_ctx_opt,
        inner_expect_opt,
        &formals,
        &type_formals,
    )?;
    if calls.is_empty() {
        return ctrue(py);
    }

    let mut parts: Vec<PyObject> = Vec::new();
    for (call_args, _loc, path, nested_refs) in calls {
        if call_args.len() != arity {
            parts.push(cfalse(py)?);
            continue;
        }
        let mut entry_ms: Vec<PyObject> = Vec::with_capacity(metrics.len());
        let mut call_ms: Vec<PyObject> = Vec::with_capacity(metrics.len());
        let mut bad = false;
        for metric in &metrics {
            let m_entry = liquefy_metric_at(py, metric.clone_ref(py), &formals, &type_formals, None)?;
            let m_call = liquefy_metric_at(py, metric.clone_ref(py), &formals, &type_formals, Some(&call_args))?;
            match (m_entry, m_call) {
                (Some(e), Some(c)) => {
                    entry_ms.push(e);
                    call_ms.push(c);
                }
                _ => {
                    bad = true;
                    break;
                }
            }
        }
        if bad {
            parts.push(cfalse(py)?);
            continue;
        }
        let lex = lexicographic_less(py, &call_ms, &entry_ms)?;
        parts.push(termination_obligation(
            py,
            &path,
            lex,
            &call_ms,
            &formals,
            &type_formals,
            &entry_refs,
            &nested_refs,
        )?);
    }
    if parts.is_empty() {
        return ctrue(py);
    }
    let mut iter = parts.into_iter();
    let mut acc = iter.next().unwrap();
    for p in iter {
        acc = new_conjunction(py, acc, p, None)?;
    }
    Ok(acc)
}

// -----------------------------------------------------------------------------
// Public Python entry points for the test suite — names follow the Python
// originals (with underscore prefix for internals).
// -----------------------------------------------------------------------------

fn name_list_from_py(py: Python<'_>, list: &Py<PyList>) -> PyResult<Vec<Py<Name>>> {
    let lb = list.bind(py);
    let mut out: Vec<Py<Name>> = Vec::with_capacity(lb.len());
    for i in 0..lb.len() {
        out.push(lb.get_item(i)?.downcast::<Name>()?.clone().unbind());
    }
    Ok(out)
}

fn obj_list_from_py(py: Python<'_>, list: &Py<PyList>) -> PyResult<Vec<PyObject>> {
    let lb = list.bind(py);
    Ok((0..lb.len()).map(|i| lb.get_item(i).map(|x| x.unbind())).collect::<PyResult<_>>()?)
}

#[pyfunction]
#[pyo3(name = "_lexicographic_less")]
pub fn py_lexicographic_less(
    py: Python<'_>,
    call_ms: Py<PyList>,
    entry_ms: Py<PyList>,
) -> PyResult<PyObject> {
    let call_v = obj_list_from_py(py, &call_ms)?;
    let entry_v = obj_list_from_py(py, &entry_ms)?;
    lexicographic_less(py, &call_v, &entry_v)
}

#[pyfunction]
#[pyo3(name = "_liquefy_metric_at", signature = (metric, formals, type_formals, call_args))]
pub fn py_liquefy_metric_at(
    py: Python<'_>,
    metric: PyObject,
    formals: Py<PyList>,
    type_formals: Py<PyList>,
    call_args: Option<Py<PyList>>,
) -> PyResult<Option<PyObject>> {
    let f = name_list_from_py(py, &formals)?;
    let tf = name_list_from_py(py, &type_formals)?;
    let ca = match call_args {
        Some(l) => Some(obj_list_from_py(py, &l)?),
        None => None,
    };
    liquefy_metric_at(py, metric, &f, &tf, ca.as_deref())
}

#[pyfunction]
#[pyo3(name = "collect_recursive_calls_with_paths", signature = (fn_name, arity, t, typing_ctx, inner_expect_ty, term_formals, type_formals))]
pub fn collect_recursive_calls_with_paths_py(
    py: Python<'_>,
    fn_name: Py<Name>,
    arity: usize,
    t: PyObject,
    typing_ctx: Option<PyObject>,
    inner_expect_ty: Option<PyObject>,
    term_formals: Py<PyList>,
    type_formals: Py<PyList>,
) -> PyResult<Py<PyList>> {
    let tf = name_list_from_py(py, &term_formals)?;
    let tyf = name_list_from_py(py, &type_formals)?;
    let calls =
        collect_recursive_calls_with_paths(py, &fn_name, arity, t, typing_ctx, inner_expect_ty, &tf, &tyf)?;
    let out = PyList::empty_bound(py);
    for (args, loc, path, nrefs) in calls {
        let args_list = PyList::new_bound(py, &args);
        let path_tuple = PyTuple::new_bound(py, &path);
        let nrefs_tuple = PyTuple::new_bound(py, &nrefs);
        out.append(PyTuple::new_bound(
            py,
            &[args_list.into_any().unbind(), loc, path_tuple.into_any().unbind(), nrefs_tuple.into_any().unbind()],
        ))?;
    }
    Ok(out.unbind())
}

#[pyfunction]
#[pyo3(name = "entry_refinement_liquids")]
pub fn entry_refinement_liquids_py(
    py: Python<'_>,
    fn_arrow_type: PyObject,
    term_formals: Py<PyList>,
    type_formals: Py<PyList>,
) -> PyResult<Py<PyList>> {
    let tf = name_list_from_py(py, &term_formals)?;
    let tyf = name_list_from_py(py, &type_formals)?;
    let v = entry_refinement_liquids(py, &fn_arrow_type, &tf, &tyf)?;
    Ok(PyList::new_bound(py, &v).unbind())
}

#[pyfunction]
#[pyo3(name = "peel_abstractions")]
pub fn peel_abstractions_py(py: Python<'_>, t: PyObject) -> PyResult<Py<PyTuple>> {
    let (names, inner) = peel_abstractions(py, t)?;
    let names_list = PyList::new_bound(py, names.iter().map(|n| n.clone_ref(py).into_any()).collect::<Vec<_>>());
    Ok(PyTuple::new_bound(py, &[names_list.into_any().unbind(), inner]).unbind())
}

#[pyfunction]
#[pyo3(name = "peel_application_chain")]
pub fn peel_application_chain_py(py: Python<'_>, t: PyObject) -> PyResult<Py<PyTuple>> {
    let (head, args) = peel_application_chain(py, t)?;
    let args_list = PyList::new_bound(py, &args);
    Ok(PyTuple::new_bound(py, &[head, args_list.into_any().unbind()]).unbind())
}

#[pyfunction]
#[pyo3(name = "peel_type_formal_names")]
pub fn peel_type_formal_names_py(py: Python<'_>, ty: PyObject) -> PyResult<Py<PyList>> {
    let names = peel_type_formal_names(py, ty)?;
    Ok(PyList::new_bound(py, names.iter().map(|n| n.clone_ref(py).into_any()).collect::<Vec<_>>()).unbind())
}

#[pyfunction]
#[pyo3(name = "substitute_formals")]
pub fn substitute_formals_py(
    py: Python<'_>,
    template: PyObject,
    formals: Py<PyList>,
    args: Py<PyList>,
) -> PyResult<PyObject> {
    let f = name_list_from_py(py, &formals)?;
    let a = obj_list_from_py(py, &args)?;
    substitute_formals(py, template, &f, &a)
}

#[allow(dead_code)]
fn _silence(_t: &Type) {
    let _ = substitution_in_type;
}
