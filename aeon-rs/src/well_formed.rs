//! Well-formedness check (port of `aeon.typechecking.well_formed`).
//!
//! `wellformed(ctx, t, k)` returns whether `t` is well-formed under `ctx`
//! at kind `k`. Used by the typechecker to validate every type that
//! reaches the constraint step.

use pyo3::prelude::*;

use crate::kind::{BaseKind, Kind, StarKind};
use crate::liquid::LiquidLiteralBool;
use crate::liquid_check::typecheck_liquid;
use crate::name::Name;
use crate::substitutions::substitution_in_liquid;
use crate::typectx::TypingContext;
use crate::types::{
    AbstractionType, ExistentialType, RefinedType, RefinementPolymorphism, Top, TypeConstructor,
    TypePolymorphism, TypeVar,
};

fn t_bool(py: Python<'_>) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: "Bool".to_string(), id: 0 })?;
    let empty = pyo3::types::PyList::empty_bound(py).unbind();
    crate::builders::new_type_constructor(py, n, empty, crate::loc::default_location(py))
}

fn star_kind(py: Python<'_>) -> PyResult<PyObject> {
    Ok(Py::new(py, (StarKind, Kind))?.into_any())
}

fn is_star(py: Python<'_>, k: &PyObject) -> bool {
    k.bind(py).downcast::<StarKind>().is_ok()
}

fn is_base(py: Python<'_>, k: &PyObject) -> bool {
    k.bind(py).downcast::<BaseKind>().is_ok()
}

fn kinds_eq(py: Python<'_>, a: &PyObject, b: &PyObject) -> PyResult<bool> {
    a.bind(py).eq(b.bind(py))
}

fn wf_inner(
    py: Python<'_>,
    ctx: &Py<TypingContext>,
    t: &PyObject,
    k: &PyObject,
) -> PyResult<bool> {
    let tb = t.bind(py);

    if tb.is_instance_of::<Top>() {
        return Ok(true);
    }

    if let Ok(rt) = tb.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let name = rt.name.clone_ref(py);
        let inner = rt.type_.clone_ref(py);
        let refinement = rt.refinement.clone_ref(py);
        drop(rt);
        let inner_b = inner.bind(py);
        if let Ok(tc) = inner_b.downcast::<TypeConstructor>() {
            let tc = tc.borrow();
            let inner_clone = inner.clone_ref(py);
            let args = tc.args.clone_ref(py);
            drop(tc);
            let args_b = args.bind(py);
            if args_b.len() > 0 {
                // RefinedType wrapping a polymorphic TypeConstructor — also fine.
                if !wf_inner(py, ctx, &inner_clone, k)? {
                    return Ok(false);
                }
            }
            let ctx_with = ctx.borrow(py).with_var(py, name, inner_clone)?;
            let ctx_with_py = Py::new(py, ctx_with)?;
            let inferred = typecheck_liquid(py, ctx_with_py.bind(py), refinement)?;
            let tb = t_bool(py)?;
            return inferred.bind(py).eq(tb.bind(py));
        }
        if let Ok(tv) = inner_b.downcast::<TypeVar>() {
            let tv = tv.borrow();
            let tvname = tv.name.clone_ref(py);
            drop(tv);
            // case RefinedType(_, TypeVar(tvname), LiquidLiteralBool(True))
            let is_lb_true = refinement
                .bind(py)
                .downcast::<LiquidLiteralBool>()
                .map(|b| b.borrow().value)
                .unwrap_or(false);
            let tvs = ctx.borrow(py).typevars(py)?;
            let tvs_b = tvs.bind(py);
            let in_vars = |target_kind: &PyObject| -> PyResult<bool> {
                for i in 0..tvs_b.len() {
                    let tup = tvs_b.get_item(i)?;
                    let en = tup.get_item(0)?.downcast::<Name>()?.borrow();
                    let target = tvname.borrow(py);
                    if en.name == target.name && en.id == target.id {
                        drop(en);
                        drop(target);
                        let ek = tup.get_item(1)?.unbind();
                        return kinds_eq(py, &ek, target_kind);
                    }
                }
                Ok(false)
            };
            if is_lb_true {
                return in_vars(k);
            }
            // case RefinedType(_, TypeVar(_), ref)
            if !is_base(py, k) {
                return Ok(false);
            }
            let bk = Py::new(py, (BaseKind, Kind))?.into_any();
            if !in_vars(&bk)? {
                return Ok(false);
            }
            // typecheck the refinement under ctx with new variable
            let inner_clone = inner.clone_ref(py);
            let ctx_with = ctx.borrow(py).with_var(py, name, inner_clone)?;
            let ctx_with_py = Py::new(py, ctx_with)?;
            let inferred = typecheck_liquid(py, ctx_with_py.bind(py), refinement)?;
            let tb = t_bool(py)?;
            return inferred.bind(py).eq(tb.bind(py));
        }
        return Ok(false);
    }

    if let Ok(tv) = tb.downcast::<TypeVar>() {
        let tvname = tv.borrow().name.clone_ref(py);
        let tvs = ctx.borrow(py).typevars(py)?;
        let tvs_b = tvs.bind(py);
        for i in 0..tvs_b.len() {
            let tup = tvs_b.get_item(i)?;
            let en = tup.get_item(0)?.downcast::<Name>()?.borrow();
            let target = tvname.borrow(py);
            if en.name == target.name && en.id == target.id {
                return Ok(true);
            }
        }
        return Ok(false);
    }

    if let Ok(at) = tb.downcast::<AbstractionType>() {
        if !is_star(py, k) {
            return Ok(false);
        }
        let at = at.borrow();
        let aname = at.var_name.clone_ref(py);
        let atype = at.var_type.clone_ref(py);
        let rtype = at.type_.clone_ref(py);
        drop(at);
        let sk = star_kind(py)?;
        if !wellformed(py, ctx, &atype, &sk)? {
            return Ok(false);
        }
        let ctx2 = ctx.borrow(py).with_var(py, aname, atype)?;
        let ctx2_py = Py::new(py, ctx2)?;
        return wellformed(py, &ctx2_py, &rtype, &sk);
    }

    if let Ok(tp) = tb.downcast::<TypePolymorphism>() {
        if !is_star(py, k) {
            return Ok(false);
        }
        let tp = tp.borrow();
        let name = tp.name.clone_ref(py);
        let kind = tp.kind.clone_ref(py);
        let body = tp.body.clone_ref(py);
        drop(tp);
        let ctx2 = ctx.borrow(py).with_typevar(py, name, kind)?;
        let ctx2_py = Py::new(py, ctx2)?;
        let sk = star_kind(py)?;
        return wellformed(py, &ctx2_py, &body, &sk);
    }

    if let Ok(rp) = tb.downcast::<RefinementPolymorphism>() {
        if !is_star(py, k) {
            return Ok(false);
        }
        let rp = rp.borrow();
        let name = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        drop(rp);
        let sk = star_kind(py)?;
        if !wellformed(py, ctx, &sort, &sk)? {
            return Ok(false);
        }
        // pred_type = AbstractionType(Name("_", 0), sort, t_bool)
        let underscore = Py::new(py, Name { name: "_".to_string(), id: 0 })?;
        let tb_obj = t_bool(py)?;
        let pred_ty = crate::builders::new_abstraction_type(
            py,
            underscore,
            sort.clone_ref(py),
            tb_obj,
            crate::loc::default_location(py),
        )?;
        let ctx2 = ctx.borrow(py).with_var(py, name, pred_ty)?;
        let ctx2_py = Py::new(py, ctx2)?;
        return wellformed(py, &ctx2_py, &body, &sk);
    }

    if let Ok(tc) = tb.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let name = tc.name.clone_ref(py);
        let args = tc.args.clone_ref(py);
        drop(tc);
        let args_b = args.bind(py);
        if args_b.len() == 0 {
            // ctx.get_type_constructor returns None when missing, the list otherwise.
            let result = ctx.borrow(py).get_type_constructor(py, name)?;
            return Ok(!result.bind(py).is_none());
        }
        let cargs = ctx.borrow(py).get_type_constructor(py, name)?;
        if cargs.bind(py).is_none() {
            return Ok(false);
        }
        let cargs_list = cargs.downcast_bound::<pyo3::types::PyList>(py);
        let Ok(cargs_b) = cargs_list else {
            return Ok(false);
        };
        if cargs_b.len() != args_b.len() {
            return Ok(false);
        }
        for i in 0..args_b.len() {
            let a = args_b.get_item(i)?.unbind();
            let sk = star_kind(py)?;
            if !wf_inner(py, ctx, &a, &sk)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }

    if let Ok(et) = tb.downcast::<ExistentialType>() {
        let et = et.borrow();
        let binders = et.binders.clone_ref(py);
        let body = et.body.clone_ref(py);
        drop(et);
        let mut ext_ctx_py = Py::new(py, clone_ctx(py, ctx)?)?;
        let binders_b = binders.bind(py);
        for i in 0..binders_b.len() {
            let tup = binders_b.get_item(i)?;
            let bn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let bt: PyObject = tup.get_item(1)?.unbind();
            let sk = star_kind(py)?;
            if !wellformed(py, &ext_ctx_py, &bt, &sk)? {
                return Ok(false);
            }
            let new_ctx = ext_ctx_py.borrow(py).with_var(py, bn, bt)?;
            ext_ctx_py = Py::new(py, new_ctx)?;
        }
        return wellformed(py, &ext_ctx_py, &body, k);
    }

    Ok(false)
}

fn clone_ctx(py: Python<'_>, ctx: &Py<TypingContext>) -> PyResult<TypingContext> {
    let cur = ctx.borrow(py);
    Ok(TypingContext {
        entries: cur.entries.clone_ref(py),
    })
}

pub fn wellformed(
    py: Python<'_>,
    ctx: &Py<TypingContext>,
    t: &PyObject,
    k: &PyObject,
) -> PyResult<bool> {
    if is_star(py, k) {
        let sk = star_kind(py)?;
        let bk = Py::new(py, (BaseKind, Kind))?.into_any();
        if wf_inner(py, ctx, t, &sk)? {
            return Ok(true);
        }
        return wf_inner(py, ctx, t, &bk);
    }
    let bk = Py::new(py, (BaseKind, Kind))?.into_any();
    wf_inner(py, ctx, t, &bk)
}

#[pyfunction]
#[pyo3(name = "wellformed", signature = (ctx, t, k = None))]
pub fn py_wellformed(
    py: Python<'_>,
    ctx: &Bound<'_, TypingContext>,
    t: PyObject,
    k: Option<PyObject>,
) -> PyResult<bool> {
    let kind = match k {
        Some(k) => k,
        None => star_kind(py)?,
    };
    let ctx_py: Py<TypingContext> = ctx.clone().unbind();
    wellformed(py, &ctx_py, &t, &kind)
}
