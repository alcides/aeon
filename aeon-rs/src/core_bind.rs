//! Name-resolution / binding pass for the *core* AST.
//! Port of `aeon.core.bind`.
//!
//! Mirrors `crate::bind` (which handles the sugar AST), but operates on
//! `crate::types::*` and `crate::terms::*` instead of `crate::sugar::*`.
//! The renaming-substitution helpers (`Subs`, `check_name`,
//! `apply_subs_name`, `clone_subs`) are reused from `crate::bind`.

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::bind::{apply_subs_name, check_name, clone_subs, Subs};
use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidTerm, LiquidVar,
};
use crate::name::Name;
use crate::terms::{
    Abstraction, Annotation, Application, Hole, If, Let, Literal, Rec, RefinementAbstraction,
    RefinementApplication, Term, TypeAbstraction, TypeApplication, Var,
};
use crate::typectx::{
    TypeBinder, TypeConstructorBinder, TypingContext, TypingContextEntry, UninterpretedBinder,
    VariableBinder,
};
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, Type, TypeConstructor,
    TypePolymorphism, TypeVar,
};

/// `bind_lq(liq, subs)` — rename references inside a LiquidTerm.
fn bind_lq(py: Python<'_>, liq: PyObject, subs: &Subs) -> PyResult<PyObject> {
    let b = liq.bind(py);

    // Literal kinds pass through unchanged.
    if b.downcast::<LiquidLiteralBool>().is_ok()
        || b.downcast::<LiquidLiteralInt>().is_ok()
        || b.downcast::<LiquidLiteralFloat>().is_ok()
        || b.downcast::<LiquidLiteralString>().is_ok()
    {
        return Ok(liq);
    }

    if let Ok(lv) = b.downcast::<LiquidVar>() {
        let lv = lv.borrow();
        let nname = apply_subs_name(py, subs, &lv.name);
        let loc = lv.loc.clone_ref(py);
        drop(lv);
        return Ok(Py::new(py, (LiquidVar { name: nname, loc }, LiquidTerm))?.into_any());
    }

    if let Ok(la) = b.downcast::<LiquidApp>() {
        let la = la.borrow();
        let nfun = apply_subs_name(py, subs, &la.fun);
        let args = la.args.clone_ref(py);
        let loc = la.loc.clone_ref(py);
        drop(la);
        let args_b = args.bind(py);
        let new_args = PyList::empty_bound(py);
        for i in 0..args_b.len() {
            let a = args_b.get_item(i)?.unbind();
            let na = bind_lq(py, a, subs)?;
            new_args.append(na)?;
        }
        return Ok(Py::new(
            py,
            (
                LiquidApp { fun: nfun, args: new_args.unbind(), loc },
                LiquidTerm,
            ),
        )?
        .into_any());
    }

    if let Ok(lh) = b.downcast::<LiquidHornApplication>() {
        let lh = lh.borrow();
        let nname = apply_subs_name(py, subs, &lh.name);
        // argtypes are passed through unchanged (the original Python does the
        // same — it doesn't substitute inside argtypes).
        let argtypes = lh.argtypes.clone_ref(py);
        let loc = lh.loc.clone_ref(py);
        drop(lh);
        return Ok(Py::new(
            py,
            (
                LiquidHornApplication { name: nname, argtypes, loc },
                LiquidTerm,
            ),
        )?
        .into_any());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Constructed {} ({}) not supported.",
        b.str()?,
        b.get_type().name()?
    )))
}

/// `bind_type(ty, subs)` — rename references inside a core Type.
fn bind_type(py: Python<'_>, ty: PyObject, subs: &mut Subs) -> PyResult<PyObject> {
    let b = ty.bind(py);

    if b.downcast::<Top>().is_ok() {
        return Ok(Py::new(py, (Top { loc: crate::loc::default_location(py) }, Type))?.into_any());
    }

    if let Ok(tv) = b.downcast::<TypeVar>() {
        let tv = tv.borrow();
        let nname = apply_subs_name(py, subs, &tv.name);
        let loc = tv.loc.clone_ref(py);
        drop(tv);
        return Ok(Py::new(py, (TypeVar { name: nname, loc }, Type))?.into_any());
    }

    if let Ok(tc) = b.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let nname = apply_subs_name(py, subs, &tc.name);
        let args = tc.args.clone_ref(py);
        let loc = tc.loc.clone_ref(py);
        drop(tc);
        let args_b = args.bind(py);
        let new_args = PyList::empty_bound(py);
        for i in 0..args_b.len() {
            let a = args_b.get_item(i)?.unbind();
            let na = bind_type(py, a, subs)?;
            new_args.append(na)?;
        }
        return Ok(Py::new(
            py,
            (
                TypeConstructor { name: nname, args: new_args.unbind(), loc },
                Type,
            ),
        )?
        .into_any());
    }

    if let Ok(at) = b.downcast::<AbstractionType>() {
        let at = at.borrow();
        let aname = at.var_name.clone_ref(py);
        let atype = at.var_type.clone_ref(py);
        let rtype = at.type_.clone_ref(py);
        let loc = at.loc.clone_ref(py);
        let mult = at.multiplicity.clone_ref(py);
        drop(at);

        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, aname, &mut nsubs)?;
        let new_atype = bind_type(py, atype, subs)?;
        let new_rtype = bind_type(py, rtype, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                AbstractionType {
                    var_name: nname,
                    var_type: new_atype,
                    type_: new_rtype,
                    loc,
                    multiplicity: mult,
                },
                Type,
            ),
        )?
        .into_any());
    }

    if let Ok(rt) = b.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let name = rt.name.clone_ref(py);
        let inner = rt.type_.clone_ref(py);
        let refn = rt.refinement.clone_ref(py);
        let loc = rt.loc.clone_ref(py);
        drop(rt);
        let nty = bind_type(py, inner, subs)?;
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nref = bind_lq(py, refn, &nsubs)?;
        // The Python `assert` requires nty be a TypeConstructor or TypeVar.
        let nty_b = nty.bind(py);
        if !(nty_b.downcast::<TypeConstructor>().is_ok() || nty_b.downcast::<TypeVar>().is_ok()) {
            return Err(pyo3::exceptions::PyAssertionError::new_err(
                "RefinedType inner must be TypeConstructor or TypeVar",
            ));
        }
        drop(nty_b);
        return Ok(Py::new(
            py,
            (
                RefinedType { name: nname, type_: nty, refinement: nref, loc },
                Type,
            ),
        )?
        .into_any());
    }

    if let Ok(tp) = b.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let name = tp.name.clone_ref(py);
        let kind = tp.kind.clone_ref(py);
        let body = tp.body.clone_ref(py);
        let loc = tp.loc.clone_ref(py);
        drop(tp);
        // The Python `name, subs = check_name(name, subs)` rebinds the
        // local subs — the caller's subs is unaffected. Clone so the
        // bound type-var name doesn't leak into sibling bindings.
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let new_body = bind_type(py, body, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                TypePolymorphism { name: nname, kind, body: new_body, loc },
                Type,
            ),
        )?
        .into_any());
    }

    if let Ok(rp) = b.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let name = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        let loc = rp.loc.clone_ref(py);
        drop(rp);
        let bound_sort = bind_type(py, sort, subs)?;
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let new_body = bind_type(py, body, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                RefinementPolymorphism { name: nname, sort: bound_sort, body: new_body, loc },
                Type,
            ),
        )?
        .into_any());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unique not supported for {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

/// `bind_term(t, subs)` — rename references inside a core Term.
fn bind_term(py: Python<'_>, t: PyObject, subs: &mut Subs) -> PyResult<PyObject> {
    let b = t.bind(py);

    if b.downcast::<Literal>().is_ok() {
        return Ok(t);
    }

    if let Ok(v) = b.downcast::<Var>() {
        let v = v.borrow();
        let nname = apply_subs_name(py, subs, &v.name);
        let loc = v.loc.clone_ref(py);
        drop(v);
        return Ok(Py::new(py, (Var { name: nname, loc }, Term))?.into_any());
    }

    if let Ok(h) = b.downcast::<Hole>() {
        let h = h.borrow();
        let name = h.name.clone_ref(py);
        let loc = h.loc.clone_ref(py);
        drop(h);
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        return Ok(Py::new(py, (Hole { name: nname, loc }, Term))?.into_any());
    }

    if let Ok(ann) = b.downcast::<Annotation>() {
        let ann = ann.borrow();
        let expr = ann.expr.clone_ref(py);
        let ty = ann.type_.clone_ref(py);
        let loc = ann.loc.clone_ref(py);
        drop(ann);
        let ne = bind_term(py, expr, subs)?;
        let nt = bind_type(py, ty, subs)?;
        return Ok(Py::new(py, (Annotation { expr: ne, type_: nt, loc }, Term))?.into_any());
    }

    if let Ok(app) = b.downcast::<Application>() {
        let app = app.borrow();
        let f = app.fun.clone_ref(py);
        let a = app.arg.clone_ref(py);
        let loc = app.loc.clone_ref(py);
        drop(app);
        let nf = bind_term(py, f, subs)?;
        let na = bind_term(py, a, subs)?;
        return Ok(Py::new(py, (Application { fun: nf, arg: na, loc }, Term))?.into_any());
    }

    if let Ok(abs) = b.downcast::<Abstraction>() {
        let abs = abs.borrow();
        let name = abs.var_name.clone_ref(py);
        let body = abs.body.clone_ref(py);
        let loc = abs.loc.clone_ref(py);
        drop(abs);
        // Python's `name, subs = check_name(name, subs)` is local — clone.
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nbody = bind_term(py, body, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (Abstraction { var_name: nname, body: nbody, loc }, Term),
        )?
        .into_any());
    }

    if let Ok(ta) = b.downcast::<TypeApplication>() {
        let ta = ta.borrow();
        let body = ta.body.clone_ref(py);
        let ty = ta.type_.clone_ref(py);
        let loc = ta.loc.clone_ref(py);
        drop(ta);
        let nb = bind_term(py, body, subs)?;
        let nt = bind_type(py, ty, subs)?;
        return Ok(Py::new(py, (TypeApplication { body: nb, type_: nt, loc }, Term))?.into_any());
    }

    if let Ok(ra) = b.downcast::<RefinementApplication>() {
        let ra = ra.borrow();
        let body = ra.body.clone_ref(py);
        let refn = ra.refinement.clone_ref(py);
        let loc = ra.loc.clone_ref(py);
        drop(ra);
        let nb = bind_term(py, body, subs)?;
        let nr = bind_term(py, refn, subs)?;
        return Ok(Py::new(
            py,
            (RefinementApplication { body: nb, refinement: nr, loc }, Term),
        )?
        .into_any());
    }

    if let Ok(tab) = b.downcast::<TypeAbstraction>() {
        let tab = tab.borrow();
        let name = tab.name.clone_ref(py);
        let kind = tab.kind.clone_ref(py);
        let body = tab.body.clone_ref(py);
        let loc = tab.loc.clone_ref(py);
        drop(tab);
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nb = bind_term(py, body, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (TypeAbstraction { name: nname, kind, body: nb, loc }, Term),
        )?
        .into_any());
    }

    if let Ok(rab) = b.downcast::<RefinementAbstraction>() {
        let rab = rab.borrow();
        let name = rab.name.clone_ref(py);
        let sort = rab.sort.clone_ref(py);
        let body = rab.body.clone_ref(py);
        let loc = rab.loc.clone_ref(py);
        drop(rab);
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nsort = bind_type(py, sort, &mut nsubs)?;
        let nb = bind_term(py, body, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                RefinementAbstraction { name: nname, sort: nsort, body: nb, loc },
                Term,
            ),
        )?
        .into_any());
    }

    if let Ok(iff) = b.downcast::<If>() {
        let iff = iff.borrow();
        let cond = iff.cond.clone_ref(py);
        let then = iff.then.clone_ref(py);
        let otherwise = iff.otherwise.clone_ref(py);
        let loc = iff.loc.clone_ref(py);
        drop(iff);
        let nc = bind_term(py, cond, subs)?;
        let nt = bind_term(py, then, subs)?;
        let no = bind_term(py, otherwise, subs)?;
        return Ok(Py::new(
            py,
            (If { cond: nc, then: nt, otherwise: no, loc }, Term),
        )?
        .into_any());
    }

    if let Ok(lt) = b.downcast::<Let>() {
        let lt = lt.borrow();
        let name = lt.var_name.clone_ref(py);
        let body = lt.var_value.clone_ref(py);
        let cont = lt.body.clone_ref(py);
        let loc = lt.loc.clone_ref(py);
        let mult = lt.multiplicity.clone_ref(py);
        drop(lt);
        let nv = bind_term(py, body, subs)?;
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nc = bind_term(py, cont, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                Let { var_name: nname, var_value: nv, body: nc, loc, multiplicity: mult },
                Term,
            ),
        )?
        .into_any());
    }

    if let Ok(rec) = b.downcast::<Rec>() {
        let rec = rec.borrow();
        let name = rec.var_name.clone_ref(py);
        let ty = rec.var_type.clone_ref(py);
        let body = rec.var_value.clone_ref(py);
        let cont = rec.body.clone_ref(py);
        let decr = rec.decreasing_by.clone_ref(py);
        let loc = rec.loc.clone_ref(py);
        let mult = rec.multiplicity.clone_ref(py);
        drop(rec);
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nty = bind_type(py, ty, &mut nsubs)?;
        let nv = bind_term(py, body, &mut nsubs)?;
        let nc = bind_term(py, cont, &mut nsubs)?;
        let decr_b = decr.bind(py);
        let mut new_decr_vec: Vec<PyObject> = Vec::with_capacity(decr_b.len());
        for i in 0..decr_b.len() {
            let item = decr_b.get_item(i)?.unbind();
            let ni = bind_term(py, item, &mut nsubs)?;
            new_decr_vec.push(ni);
        }
        let new_decr = PyTuple::new_bound(py, new_decr_vec).unbind();
        return Ok(Py::new(
            py,
            (
                Rec {
                    var_name: nname,
                    var_type: nty,
                    var_value: nv,
                    body: nc,
                    decreasing_by: new_decr,
                    loc,
                    multiplicity: mult,
                },
                Term,
            ),
        )?
        .into_any());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unique not supported for {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

/// `bind_ctx(ctx, subs) -> (ctx, subs)` — rename binder occurrences,
/// recurse into entry types. The original Python re-initialises `subs`
/// to `[]` at the top of this function (likely a bug, but we preserve it).
fn bind_ctx(
    py: Python<'_>,
    ctx: &TypingContext,
    _initial_subs: Subs,
) -> PyResult<(Py<TypingContext>, Subs)> {
    let entries = ctx.entries.bind(py);
    let new_entries = PyList::empty_bound(py);
    let mut subs: Subs = Vec::new();

    for i in 0..entries.len() {
        let entry = entries.get_item(i)?;

        if let Ok(vb) = entry.downcast::<VariableBinder>() {
            let vb = vb.borrow();
            let name = vb.name.clone_ref(py);
            let ty = vb.type_.clone_ref(py);
            drop(vb);
            let nname = check_name(py, name, &mut subs)?;
            let nty = bind_type(py, ty, &mut subs)?;
            let pe = Py::new(
                py,
                (
                    VariableBinder { name: nname, type_: nty },
                    TypingContextEntry,
                ),
            )?;
            new_entries.append(pe)?;
        } else if let Ok(ub) = entry.downcast::<UninterpretedBinder>() {
            let ub = ub.borrow();
            let name = ub.name.clone_ref(py);
            let ty = ub.type_.clone_ref(py);
            drop(ub);
            let nname = check_name(py, name, &mut subs)?;
            let nty = bind_type(py, ty, &mut subs)?;
            // Python asserts that nty is an AbstractionType.
            let nty_b = nty.bind(py);
            if nty_b.downcast::<AbstractionType>().is_err() {
                return Err(pyo3::exceptions::PyAssertionError::new_err(
                    "UninterpretedBinder.type must lower to AbstractionType",
                ));
            }
            drop(nty_b);
            let pe = Py::new(
                py,
                (
                    UninterpretedBinder { name: nname, type_: nty },
                    TypingContextEntry,
                ),
            )?;
            new_entries.append(pe)?;
        } else if let Ok(tb) = entry.downcast::<TypeBinder>() {
            let tb = tb.borrow();
            let name = tb.type_name.clone_ref(py);
            let kind = tb.type_kind.clone_ref(py);
            drop(tb);
            let nname = check_name(py, name, &mut subs)?;
            let pe = Py::new(
                py,
                (
                    TypeBinder { type_name: nname, type_kind: kind },
                    TypingContextEntry,
                ),
            )?;
            new_entries.append(pe)?;
        } else if let Ok(cb) = entry.downcast::<TypeConstructorBinder>() {
            let cb = cb.borrow();
            let name = cb.name.clone_ref(py);
            let args = cb.args.clone_ref(py);
            drop(cb);
            let nname = check_name(py, name, &mut subs)?;
            let pe = Py::new(
                py,
                (
                    TypeConstructorBinder { name: nname, args },
                    TypingContextEntry,
                ),
            )?;
            new_entries.append(pe)?;
        } else {
            return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                "Unique not supported for {} ({})",
                entry.str()?,
                entry.get_type().name()?
            )));
        }
    }

    // Use the public constructor so __new__ runs (prepends builtin types).
    let tc_cls = py.get_type_bound::<TypingContext>();
    let tc = tc_cls.call1((new_entries.unbind(),))?;
    let tc_py: Py<TypingContext> = tc.downcast::<TypingContext>()?.clone().unbind();
    Ok((tc_py, subs))
}

// ---- Python-facing functions --------------------------------------------

#[pyfunction]
pub fn py_bind_lq(py: Python<'_>, liq: PyObject, subs: Vec<(String, Py<Name>)>) -> PyResult<PyObject> {
    bind_lq(py, liq, &subs)
}

#[pyfunction]
pub fn py_bind_type(py: Python<'_>, ty: PyObject, subs: Vec<(String, Py<Name>)>) -> PyResult<PyObject> {
    let mut subs = subs;
    bind_type(py, ty, &mut subs)
}

#[pyfunction]
pub fn py_bind_term(py: Python<'_>, t: PyObject, subs: Vec<(String, Py<Name>)>) -> PyResult<PyObject> {
    let mut subs = subs;
    bind_term(py, t, &mut subs)
}

#[pyfunction]
pub fn py_bind_ctx(
    py: Python<'_>,
    ctx: &TypingContext,
    subs: Vec<(String, Py<Name>)>,
) -> PyResult<(Py<TypingContext>, Vec<(String, Py<Name>)>)> {
    bind_ctx(py, ctx, subs)
}

/// `bind_ids(ctx, t) -> (ctx, t)` — top-level entry; resets subs to empty
/// before rebinding both ctx and t.
#[pyfunction]
pub fn bind_ids(
    py: Python<'_>,
    ctx: &TypingContext,
    t: PyObject,
) -> PyResult<(Py<TypingContext>, PyObject)> {
    let (new_ctx, mut subs) = bind_ctx(py, ctx, Vec::new())?;
    let nt = bind_term(py, t, &mut subs)?;
    Ok((new_ctx, nt))
}
