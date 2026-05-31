//! Alpha-equivalence equality and canonicalization for core types and
//! terms — port of `aeon.core.equality`.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};
use std::collections::HashMap;

use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidLiteralUnit, LiquidTerm, LiquidVar,
};
use crate::name::Name;
use crate::terms::{
    Abstraction, Application, If, Let, Literal, Rec, RefinementAbstraction, RefinementApplication,
    Term, TypeAbstraction, TypeApplication, Var,
};
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, Type, TypeConstructor,
    TypePolymorphism, TypeVar,
};

// ---- Rename map (dict[Name, Name]) -------------------------------------

#[derive(Clone, PartialEq, Eq, Hash)]
struct NameKey {
    name: String,
    id: i64,
}

fn name_key(py: Python<'_>, n: &Py<Name>) -> NameKey {
    let b = n.borrow(py);
    NameKey { name: b.name.clone(), id: b.id }
}

type Renames = HashMap<NameKey, Py<Name>>;

fn renames_from(py: Python<'_>, d: Option<Py<PyDict>>) -> PyResult<Renames> {
    let mut out: Renames = HashMap::new();
    if let Some(d) = d {
        for (k, v) in d.bind(py).iter() {
            let k_n: Py<Name> = k.downcast::<Name>()?.clone().unbind();
            let v_n: Py<Name> = v.downcast::<Name>()?.clone().unbind();
            out.insert(name_key(py, &k_n), v_n);
        }
    }
    Ok(out)
}

fn renames_extend(py: Python<'_>, base: &Renames, k: Py<Name>, v: Py<Name>) -> Renames {
    // Manual deep clone because Py<Name> isn't Clone.
    let mut deep: Renames = HashMap::with_capacity(base.len() + 1);
    for (k, v) in base.iter() {
        deep.insert(k.clone(), v.clone_ref(py));
    }
    deep.insert(name_key(py, &k), v);
    deep
}

fn rename_lookup(py: Python<'_>, renames: &Renames, n: &Py<Name>) -> Py<Name> {
    let k = name_key(py, n);
    if let Some(v) = renames.get(&k) {
        return v.clone_ref(py);
    }
    n.clone_ref(py)
}

fn name_eq(py: Python<'_>, a: &Py<Name>, b: &Py<Name>) -> bool {
    let a = a.borrow(py);
    let b = b.borrow(py);
    a.name == b.name && a.id == b.id
}

// ---- core_liquid_equality ----------------------------------------------

fn cle(py: Python<'_>, lq1: PyObject, lq2: PyObject, renames: &Renames) -> PyResult<bool> {
    let a = lq1.bind(py);
    let b = lq2.bind(py);
    if let (Ok(va), Ok(vb)) = (a.downcast::<LiquidVar>(), b.downcast::<LiquidVar>()) {
        let renamed = rename_lookup(py, renames, &va.borrow().name);
        return Ok(name_eq(py, &renamed, &vb.borrow().name));
    }
    if let (Ok(la), Ok(lb)) = (
        a.downcast::<LiquidLiteralBool>(),
        b.downcast::<LiquidLiteralBool>(),
    ) {
        return Ok(la.borrow().value == lb.borrow().value);
    }
    if let (Ok(la), Ok(lb)) = (
        a.downcast::<LiquidLiteralInt>(),
        b.downcast::<LiquidLiteralInt>(),
    ) {
        return Ok(la.borrow().value == lb.borrow().value);
    }
    if let (Ok(la), Ok(lb)) = (
        a.downcast::<LiquidLiteralFloat>(),
        b.downcast::<LiquidLiteralFloat>(),
    ) {
        return Ok(la.borrow().value == lb.borrow().value);
    }
    if let (Ok(la), Ok(lb)) = (
        a.downcast::<LiquidLiteralString>(),
        b.downcast::<LiquidLiteralString>(),
    ) {
        return Ok(la.borrow().value == lb.borrow().value);
    }
    if a.downcast::<LiquidLiteralUnit>().is_ok() && b.downcast::<LiquidLiteralUnit>().is_ok() {
        return Ok(true);
    }
    if let (Ok(aa), Ok(ab)) = (a.downcast::<LiquidApp>(), b.downcast::<LiquidApp>()) {
        let aa = aa.borrow();
        let ab = ab.borrow();
        if !name_eq(py, &aa.fun, &ab.fun) {
            return Ok(false);
        }
        let args_a = aa.args.bind(py);
        let args_b = ab.args.bind(py);
        if args_a.len() != args_b.len() {
            return Ok(false);
        }
        for i in 0..args_a.len() {
            let x = args_a.get_item(i)?.unbind();
            let y = args_b.get_item(i)?.unbind();
            if !cle(py, x, y, renames)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if let (Ok(ha), Ok(hb)) = (
        a.downcast::<LiquidHornApplication>(),
        b.downcast::<LiquidHornApplication>(),
    ) {
        let ha = ha.borrow();
        let hb = hb.borrow();
        return Ok(name_eq(py, &ha.name, &hb.name));
    }
    Ok(false)
}

#[pyfunction]
#[pyo3(signature = (lq1, lq2, rename_left = None))]
pub fn core_liquid_equality(
    py: Python<'_>,
    lq1: PyObject,
    lq2: PyObject,
    rename_left: Option<Py<PyDict>>,
) -> PyResult<bool> {
    let renames = renames_from(py, rename_left)?;
    cle(py, lq1, lq2, &renames)
}

// ---- core_type_equality ------------------------------------------------

fn cte(py: Python<'_>, t1: PyObject, t2: PyObject, renames: &Renames) -> PyResult<bool> {
    let a = t1.bind(py);
    let b = t2.bind(py);

    if let (Ok(va), Ok(vb)) = (a.downcast::<TypeVar>(), b.downcast::<TypeVar>()) {
        let renamed = rename_lookup(py, renames, &va.borrow().name);
        return Ok(name_eq(py, &renamed, &vb.borrow().name));
    }
    if let (Ok(ra), Ok(rb)) = (a.downcast::<RefinedType>(), b.downcast::<RefinedType>()) {
        let ra = ra.borrow();
        let rb = rb.borrow();
        let ty_eq = cte(py, ra.type_.clone_ref(py), rb.type_.clone_ref(py), renames)?;
        if !ty_eq {
            return Ok(false);
        }
        let bound_left = ra.name.clone_ref(py);
        let bound_right = rb.name.clone_ref(py);
        let nr = renames_extend(py, renames, bound_left, bound_right);
        return cle(py, ra.refinement.clone_ref(py), rb.refinement.clone_ref(py), &nr);
    }
    if let (Ok(aa), Ok(bb)) = (a.downcast::<AbstractionType>(), b.downcast::<AbstractionType>()) {
        let aa = aa.borrow();
        let bb = bb.borrow();
        let p1 = cte(py, aa.var_type.clone_ref(py), bb.var_type.clone_ref(py), renames)?;
        if !p1 {
            return Ok(false);
        }
        let bound_left = aa.var_name.clone_ref(py);
        let bound_right = bb.var_name.clone_ref(py);
        let nr = renames_extend(py, renames, bound_left, bound_right);
        return cte(py, aa.type_.clone_ref(py), bb.type_.clone_ref(py), &nr);
    }
    if let (Ok(ca), Ok(cb)) = (
        a.downcast::<TypeConstructor>(),
        b.downcast::<TypeConstructor>(),
    ) {
        let ca = ca.borrow();
        let cb = cb.borrow();
        if !name_eq(py, &ca.name, &cb.name) {
            return Ok(false);
        }
        let args_a = ca.args.bind(py);
        let args_b = cb.args.bind(py);
        if args_a.len() != args_b.len() {
            return Ok(false);
        }
        for i in 0..args_a.len() {
            let x = args_a.get_item(i)?.unbind();
            let y = args_b.get_item(i)?.unbind();
            if !cte(py, x, y, renames)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if let (Ok(pa), Ok(pb)) = (
        a.downcast::<TypePolymorphism>(),
        b.downcast::<TypePolymorphism>(),
    ) {
        let pa = pa.borrow();
        let pb = pb.borrow();
        // Compare kinds via Python __eq__.
        if !pa.kind.bind(py).eq(pb.kind.bind(py))? {
            return Ok(false);
        }
        let bound_left = pa.name.clone_ref(py);
        let bound_right = pb.name.clone_ref(py);
        let nr = renames_extend(py, renames, bound_left, bound_right);
        return cte(py, pa.body.clone_ref(py), pb.body.clone_ref(py), &nr);
    }
    if let (Ok(pa), Ok(pb)) = (
        a.downcast::<RefinementPolymorphism>(),
        b.downcast::<RefinementPolymorphism>(),
    ) {
        let pa = pa.borrow();
        let pb = pb.borrow();
        let sort_eq = cte(py, pa.sort.clone_ref(py), pb.sort.clone_ref(py), renames)?;
        if !sort_eq {
            return Ok(false);
        }
        let bound_left = pa.name.clone_ref(py);
        let bound_right = pb.name.clone_ref(py);
        let nr = renames_extend(py, renames, bound_left, bound_right);
        return cte(py, pa.body.clone_ref(py), pb.body.clone_ref(py), &nr);
    }
    if a.downcast::<Top>().is_ok() && b.downcast::<Top>().is_ok() {
        return Ok(true);
    }
    Ok(false)
}

#[pyfunction]
#[pyo3(signature = (type1, type2, rename_left = None))]
pub fn core_type_equality(
    py: Python<'_>,
    type1: PyObject,
    type2: PyObject,
    rename_left: Option<Py<PyDict>>,
) -> PyResult<bool> {
    let renames = renames_from(py, rename_left)?;
    cte(py, type1, type2, &renames)
}

// ---- canonicalize_type --------------------------------------------------
//
// Renames every binder (and its bound occurrences) to a positional name
// `Name("__c<N>__", 0)` from a single shared pre-order counter, so two
// types are alpha-equivalent iff their canonical forms compare structurally
// equal via the dataclass-style `__eq__`/`__hash__`.

fn fresh_canonical(py: Python<'_>, counter: &mut i64) -> PyResult<Py<Name>> {
    let id = *counter;
    *counter += 1;
    Py::new(py, Name { name: format!("__c{}__", id), id: 0 })
}

fn rename_liquid(
    py: Python<'_>,
    lq: PyObject,
    mapping: &Renames,
) -> PyResult<PyObject> {
    // Apply substitution_in_liquid for each (old, new) pair.
    let mut cur = lq;
    for (old_key, new_name) in mapping.iter() {
        // Build the old Name back from its key.
        let old = Py::new(
            py,
            Name { name: old_key.name.clone(), id: old_key.id },
        )?;
        let lv = Py::new(
            py,
            (
                LiquidVar {
                    name: new_name.clone_ref(py),
                    loc: crate::loc::default_location(py),
                },
                LiquidTerm,
            ),
        )?;
        cur = crate::substitutions::substitution_in_liquid(py, cur, lv.into_any(), old)?;
    }
    Ok(cur)
}

fn ct(py: Python<'_>, ty: PyObject, renames: &Renames, counter: &mut i64) -> PyResult<PyObject> {
    let b = ty.bind(py);

    if let Ok(tv) = b.downcast::<TypeVar>() {
        let renamed = rename_lookup(py, renames, &tv.borrow().name);
        return Ok(Py::new(
            py,
            (
                TypeVar { name: renamed, loc: crate::loc::default_location(py) },
                Type,
            ),
        )?
        .into_any());
    }
    if let Ok(tc) = b.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let name = tc.name.clone_ref(py);
        let args = tc.args.clone_ref(py);
        drop(tc);
        let new_args = PyList::empty_bound(py);
        let args_b = args.bind(py);
        for i in 0..args_b.len() {
            let item = args_b.get_item(i)?.unbind();
            let ci = ct(py, item, renames, counter)?;
            new_args.append(ci)?;
        }
        return Ok(Py::new(
            py,
            (
                TypeConstructor {
                    name,
                    args: new_args.unbind(),
                    loc: crate::loc::default_location(py),
                },
                Type,
            ),
        )?
        .into_any());
    }
    if let Ok(at) = b.downcast::<AbstractionType>() {
        let at = at.borrow();
        let var_name = at.var_name.clone_ref(py);
        let var_type = at.var_type.clone_ref(py);
        let ret_type = at.type_.clone_ref(py);
        let mult = at.multiplicity.clone_ref(py);
        drop(at);
        let c_var_type = ct(py, var_type, renames, counter)?;
        let fresh = fresh_canonical(py, counter)?;
        let nr = renames_extend(py, renames, var_name, fresh.clone_ref(py));
        let c_ret_type = ct(py, ret_type, &nr, counter)?;
        return Ok(Py::new(
            py,
            (
                AbstractionType {
                    var_name: fresh,
                    var_type: c_var_type,
                    type_: c_ret_type,
                    loc: crate::loc::default_location(py),
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
        drop(rt);
        let c_inner = ct(py, inner, renames, counter)?;
        let fresh = fresh_canonical(py, counter)?;
        // Rebind the refinement's bound var to `fresh`, then apply the
        // outer renames.
        let lv = Py::new(
            py,
            (
                LiquidVar {
                    name: fresh.clone_ref(py),
                    loc: crate::loc::default_location(py),
                },
                LiquidTerm,
            ),
        )?;
        let c_ref = crate::substitutions::substitution_in_liquid(
            py,
            refn,
            lv.into_any(),
            name,
        )?;
        let c_ref = rename_liquid(py, c_ref, renames)?;
        return Ok(Py::new(
            py,
            (
                RefinedType {
                    name: fresh,
                    type_: c_inner,
                    refinement: c_ref,
                    loc: crate::loc::default_location(py),
                },
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
        drop(tp);
        let fresh = fresh_canonical(py, counter)?;
        let nr = renames_extend(py, renames, name, fresh.clone_ref(py));
        let c_body = ct(py, body, &nr, counter)?;
        return Ok(Py::new(
            py,
            (
                TypePolymorphism {
                    name: fresh,
                    kind,
                    body: c_body,
                    loc: crate::loc::default_location(py),
                },
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
        drop(rp);
        let c_sort = ct(py, sort, renames, counter)?;
        let fresh = fresh_canonical(py, counter)?;
        let nr = renames_extend(py, renames, name, fresh.clone_ref(py));
        let c_body = ct(py, body, &nr, counter)?;
        return Ok(Py::new(
            py,
            (
                RefinementPolymorphism {
                    name: fresh,
                    sort: c_sort,
                    body: c_body,
                    loc: crate::loc::default_location(py),
                },
                Type,
            ),
        )?
        .into_any());
    }
    if b.downcast::<Top>().is_ok() {
        return Ok(ty);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unsupported type in canonicalize_type: {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

#[pyfunction]
#[pyo3(signature = (ty, rename = None, counter = None))]
pub fn canonicalize_type(
    py: Python<'_>,
    ty: PyObject,
    rename: Option<Py<PyDict>>,
    counter: Option<Py<PyList>>,
) -> PyResult<PyObject> {
    let renames = renames_from(py, rename)?;
    // Counter is a one-element list (Python mutable int trick).
    let mut local_counter: i64 = 0;
    let counter_list = counter;
    if let Some(c) = counter_list.as_ref() {
        let cb = c.bind(py);
        if cb.len() > 0 {
            local_counter = cb.get_item(0)?.extract::<i64>()?;
        }
    }
    let out = ct(py, ty, &renames, &mut local_counter)?;
    if let Some(c) = counter_list.as_ref() {
        let cb = c.bind(py);
        if cb.len() > 0 {
            cb.set_item(0, local_counter)?;
        } else {
            cb.append(local_counter)?;
        }
    }
    Ok(out)
}

// ---- core_term_equality -------------------------------------------------

fn ctm(py: Python<'_>, t1: PyObject, t2: PyObject, renames: &Renames) -> PyResult<bool> {
    let a = t1.bind(py);
    let b = t2.bind(py);

    if let (Ok(va), Ok(vb)) = (a.downcast::<Var>(), b.downcast::<Var>()) {
        let renamed = rename_lookup(py, renames, &va.borrow().name);
        return Ok(name_eq(py, &renamed, &vb.borrow().name));
    }
    if let (Ok(la), Ok(lb)) = (a.downcast::<Literal>(), b.downcast::<Literal>()) {
        let la = la.borrow();
        let lb = lb.borrow();
        let v_eq = la.value.bind(py).eq(lb.value.bind(py))?;
        if !v_eq {
            return Ok(false);
        }
        return cte(py, la.type_.clone_ref(py), lb.type_.clone_ref(py), renames);
    }
    if let (Ok(aa), Ok(ab)) = (a.downcast::<Application>(), b.downcast::<Application>()) {
        let aa = aa.borrow();
        let ab = ab.borrow();
        let p1 = ctm(py, aa.fun.clone_ref(py), ab.fun.clone_ref(py), renames)?;
        if !p1 {
            return Ok(false);
        }
        return ctm(py, aa.arg.clone_ref(py), ab.arg.clone_ref(py), renames);
    }
    if let (Ok(aa), Ok(ab)) = (a.downcast::<Abstraction>(), b.downcast::<Abstraction>()) {
        let aa = aa.borrow();
        let ab = ab.borrow();
        let nr = renames_extend(py, renames, aa.var_name.clone_ref(py), ab.var_name.clone_ref(py));
        return ctm(py, aa.body.clone_ref(py), ab.body.clone_ref(py), &nr);
    }
    if let (Ok(la), Ok(lb)) = (a.downcast::<Let>(), b.downcast::<Let>()) {
        let la = la.borrow();
        let lb = lb.borrow();
        let val_eq = ctm(py, la.var_value.clone_ref(py), lb.var_value.clone_ref(py), renames)?;
        if !val_eq {
            return Ok(false);
        }
        let nr = renames_extend(py, renames, la.var_name.clone_ref(py), lb.var_name.clone_ref(py));
        return ctm(py, la.body.clone_ref(py), lb.body.clone_ref(py), &nr);
    }
    if let (Ok(ra), Ok(rb)) = (a.downcast::<Rec>(), b.downcast::<Rec>()) {
        let ra = ra.borrow();
        let rb = rb.borrow();
        let nr = renames_extend(py, renames, ra.var_name.clone_ref(py), rb.var_name.clone_ref(py));
        let val_eq = ctm(py, ra.var_value.clone_ref(py), rb.var_value.clone_ref(py), &nr)?;
        if !val_eq {
            return Ok(false);
        }
        let ty_eq = cte(py, ra.var_type.clone_ref(py), rb.var_type.clone_ref(py), renames)?;
        if !ty_eq {
            return Ok(false);
        }
        let cont_eq = ctm(py, ra.body.clone_ref(py), rb.body.clone_ref(py), &nr)?;
        if !cont_eq {
            return Ok(false);
        }
        let dec_a = ra.decreasing_by.bind(py);
        let dec_b = rb.decreasing_by.bind(py);
        if dec_a.len() != dec_b.len() {
            return Ok(false);
        }
        for i in 0..dec_a.len() {
            let x = dec_a.get_item(i)?.unbind();
            let y = dec_b.get_item(i)?.unbind();
            if !ctm(py, x, y, &nr)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if let (Ok(ia), Ok(ib)) = (a.downcast::<If>(), b.downcast::<If>()) {
        let ia = ia.borrow();
        let ib = ib.borrow();
        let p1 = ctm(py, ia.cond.clone_ref(py), ib.cond.clone_ref(py), renames)?;
        if !p1 {
            return Ok(false);
        }
        let p2 = ctm(py, ia.then.clone_ref(py), ib.then.clone_ref(py), renames)?;
        if !p2 {
            return Ok(false);
        }
        return ctm(py, ia.otherwise.clone_ref(py), ib.otherwise.clone_ref(py), renames);
    }
    if let (Ok(taa), Ok(tab)) = (a.downcast::<TypeApplication>(), b.downcast::<TypeApplication>())
    {
        let taa = taa.borrow();
        let tab = tab.borrow();
        let p1 = ctm(py, taa.body.clone_ref(py), tab.body.clone_ref(py), renames)?;
        if !p1 {
            return Ok(false);
        }
        return cte(py, taa.type_.clone_ref(py), tab.type_.clone_ref(py), renames);
    }
    if let (Ok(taa), Ok(tab)) = (
        a.downcast::<TypeAbstraction>(),
        b.downcast::<TypeAbstraction>(),
    ) {
        let taa = taa.borrow();
        let tab = tab.borrow();
        if !taa.kind.bind(py).eq(tab.kind.bind(py))? {
            return Ok(false);
        }
        let nr = renames_extend(py, renames, taa.name.clone_ref(py), tab.name.clone_ref(py));
        return ctm(py, taa.body.clone_ref(py), tab.body.clone_ref(py), &nr);
    }
    if let (Ok(ra), Ok(rb)) = (
        a.downcast::<RefinementAbstraction>(),
        b.downcast::<RefinementAbstraction>(),
    ) {
        let ra = ra.borrow();
        let rb = rb.borrow();
        let sort_eq = cte(py, ra.sort.clone_ref(py), rb.sort.clone_ref(py), renames)?;
        if !sort_eq {
            return Ok(false);
        }
        let nr = renames_extend(py, renames, ra.name.clone_ref(py), rb.name.clone_ref(py));
        return ctm(py, ra.body.clone_ref(py), rb.body.clone_ref(py), &nr);
    }
    if let (Ok(ra), Ok(rb)) = (
        a.downcast::<RefinementApplication>(),
        b.downcast::<RefinementApplication>(),
    ) {
        let ra = ra.borrow();
        let rb = rb.borrow();
        let p1 = ctm(py, ra.body.clone_ref(py), rb.body.clone_ref(py), renames)?;
        if !p1 {
            return Ok(false);
        }
        return ctm(py, ra.refinement.clone_ref(py), rb.refinement.clone_ref(py), renames);
    }
    Ok(false)
}

#[pyfunction]
#[pyo3(signature = (term1, term2, rename_left = None))]
pub fn core_term_equality(
    py: Python<'_>,
    term1: PyObject,
    term2: PyObject,
    rename_left: Option<Py<PyDict>>,
) -> PyResult<bool> {
    let renames = renames_from(py, rename_left)?;
    ctm(py, term1, term2, &renames)
}
