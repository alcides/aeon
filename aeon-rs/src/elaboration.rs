//! Sugar-level elaboration: bidirectional type unification + polar-variable
//! removal.
//! Port of `aeon.elaboration.__init__`.
//!
//! The algorithm uses three mutable SType subclasses (UnificationVar, Union,
//! Intersection) whose list fields are mutated in place during unification.
//! In Rust we use `Py<PyList>` for these and mutate via `.bind(py).append(...)`
//! / `.set_item(...)`.

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::elab_inst::sugar_type_substitution;
use crate::elabctx::ElaborationTypingContext;

use crate::loc::{default_location, resolve_loc};
use crate::name::{next_fresh_id, Name};
use crate::sugar::{
    SAbstraction, SAbstractionType, SAnnotation, SAnonConstructor, SApplication, SHole, SIf,
    SLet, SLiteral, SRec, SRefinedType, SRefinementAbstraction, SRefinementApplication,
    SRefinementPolymorphism, STerm, STypeAbstraction, STypeApplication, STypeConstructor,
    STypePolymorphism, STypeVar, SType, SVar,
};
use crate::sugar_helpers::{substitute_refinement_param_in_stype, substitution_sterm_in_stype};

// =============================================================================
// SType subclasses used by elaboration.
// =============================================================================

#[pyclass(module = "aeon_rs", extends = SType)]
pub struct UnificationVar {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set)]
    pub lower: Py<PyList>,
    #[pyo3(get, set)]
    pub upper: Py<PyList>,
    #[pyo3(get, set)]
    pub loc: PyObject,
}

#[pymethods]
impl UnificationVar {
    #[new]
    #[pyo3(signature = (name, lower = None, upper = None, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        lower: Option<Py<PyList>>,
        upper: Option<Py<PyList>>,
        loc: Option<PyObject>,
    ) -> (Self, SType) {
        let lower = lower.unwrap_or_else(|| PyList::empty_bound(py).unbind());
        let upper = upper.unwrap_or_else(|| PyList::empty_bound(py).unbind());
        (
            UnificationVar { name, lower, upper, loc: resolve_loc(py, loc) },
            SType,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "lower", "upper"])
    }

    fn __str__(&self, py: Python<'_>) -> String {
        format!("?{}", self.name.borrow(py).__str__())
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!("UnificationVar({})", self.name.borrow(py).__str__())
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> bool {
        // Identity-by-name eq (mirrors dataclass default which would also
        // compare lower/upper but those mutate). The algorithm only uses
        // `==` in narrow ways: collection membership tests on UnificationVar
        // identity. Name-id comparison is sufficient.
        match other.downcast::<UnificationVar>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                a.name == b.name && a.id == b.id
            }
            Err(_) => false,
        }
    }

    fn __hash__(&self, py: Python<'_>) -> u64 {
        let n = self.name.borrow(py);
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        h.finish()
    }

    /// Equivalent of Python's `constrain_upper`. Not used by the Rust
    /// algorithm itself but kept for parity with `aeon.elaboration`.
    fn constrain_upper(&self, py: Python<'_>, ty: PyObject) -> PyResult<()> {
        let bty = base(py, ty)?;
        self.upper.bind(py).append(bty)?;
        Ok(())
    }
}

#[pyclass(module = "aeon_rs", extends = SType)]
pub struct Union {
    #[pyo3(get, set)]
    pub united: Py<PyList>,
    #[pyo3(get, set)]
    pub loc: PyObject,
}

#[pymethods]
impl Union {
    #[new]
    #[pyo3(signature = (united, loc = None))]
    fn py_new(py: Python<'_>, united: Py<PyList>, loc: Option<PyObject>) -> (Self, SType) {
        (Union { united, loc: resolve_loc(py, loc) }, SType)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["united"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let l = self.united.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            parts.push(l.get_item(i)?.str()?.to_string());
        }
        Ok(format!("Union({})", parts.join(", ")))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        let s = self.__str__(py)?;
        s.hash(&mut h);
        Ok(h.finish())
    }
}

#[pyclass(module = "aeon_rs", extends = SType)]
pub struct Intersection {
    #[pyo3(get, set)]
    pub intersected: Py<PyList>,
    #[pyo3(get, set)]
    pub loc: PyObject,
}

#[pymethods]
impl Intersection {
    #[new]
    #[pyo3(signature = (intersected, loc = None))]
    fn py_new(py: Python<'_>, intersected: Py<PyList>, loc: Option<PyObject>) -> (Self, SType) {
        (
            Intersection { intersected, loc: resolve_loc(py, loc) },
            SType,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["intersected"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let l = self.intersected.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            parts.push(l.get_item(i)?.str()?.to_string());
        }
        Ok(format!("Intersection({})", parts.join(", ")))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        let s = self.__str__(py)?;
        s.hash(&mut h);
        Ok(h.finish())
    }
}

// =============================================================================
// Helpers / error construction.
// =============================================================================

fn raise_api(py: Python<'_>, cls: &str, args: Vec<PyObject>) -> PyErr {
    let result: PyResult<PyErr> = (|| {
        let api = py.import_bound("aeon.facade.api")?;
        let cls_obj = api.getattr(cls)?;
        let tup = PyTuple::new_bound(py, &args);
        let err_inst = cls_obj.call1(tup)?;
        Ok(PyErr::from_value_bound(err_inst))
    })();
    result.unwrap_or_else(|e| e)
}

fn todo_hole(py: Python<'_>) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: "todo".to_string(), id: -1 })?;
    let hole = Py::new(
        py,
        (
            SHole { name: n, loc: default_location(py) },
            STerm,
        ),
    )?;
    Ok(hole.into_any())
}

fn fresh_named(py: Python<'_>, prefix: &str) -> PyResult<Py<Name>> {
    let id = next_fresh_id(py)?;
    Py::new(py, Name { name: prefix.to_string(), id })
}

fn mk_type_ctor(py: Python<'_>, name: &str) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: name.to_string(), id: 0 })?;
    let stc = Py::new(
        py,
        (
            STypeConstructor {
                name: n,
                args: PyList::empty_bound(py).unbind(),
                loc: default_location(py),
            },
            SType,
        ),
    )?;
    Ok(stc.into_any())
}

fn st_top(py: Python<'_>) -> PyResult<PyObject> {
    mk_type_ctor(py, "Top")
}
fn st_unit(py: Python<'_>) -> PyResult<PyObject> {
    mk_type_ctor(py, "Unit")
}
fn st_bool(py: Python<'_>) -> PyResult<PyObject> {
    mk_type_ctor(py, "Bool")
}

fn mk_base_kind(py: Python<'_>) -> PyResult<PyObject> {
    Ok(crate::kind::base(py))
}

fn mk_unification_var(py: Python<'_>, name: Py<Name>) -> PyResult<PyObject> {
    let uv = Py::new(
        py,
        (
            UnificationVar {
                name,
                lower: PyList::empty_bound(py).unbind(),
                upper: PyList::empty_bound(py).unbind(),
                loc: default_location(py),
            },
            SType,
        ),
    )?;
    Ok(uv.into_any())
}

fn mk_type_app(py: Python<'_>, body: PyObject, ty: PyObject) -> PyResult<PyObject> {
    let ta = Py::new(
        py,
        (
            STypeApplication { body, type_: ty, loc: default_location(py) },
            STerm,
        ),
    )?;
    Ok(ta.into_any())
}

// =============================================================================
// base / _extract_base_type_name
// =============================================================================

fn base(py: Python<'_>, ty: PyObject) -> PyResult<PyObject> {
    let b = ty.bind(py);
    if let Ok(srt) = b.downcast::<SRefinedType>() {
        return Ok(srt.borrow().type_.clone_ref(py));
    }
    Ok(ty)
}

fn extract_base_type_name(py: Python<'_>, ty: &PyObject) -> PyResult<Option<String>> {
    let b = ty.bind(py);
    if let Ok(stc) = b.downcast::<STypeConstructor>() {
        let stc = stc.borrow();
        return Ok(Some(stc.name.borrow(py).name.clone()));
    }
    if let Ok(srt) = b.downcast::<SRefinedType>() {
        let inner = srt.borrow().type_.clone_ref(py);
        return extract_base_type_name(py, &inner);
    }
    Ok(None)
}

// =============================================================================
// elaborate_foralls
// =============================================================================

fn get_type_vars(py: Python<'_>, ty: &PyObject) -> PyResult<Vec<PyObject>> {
    // Call into the Python helper. The result is a Python set of STypeVar.
    let m = py.import_bound("aeon.sugar.stypes")?;
    let r = m.getattr("get_type_vars")?.call1((ty.clone_ref(py),))?;
    let mut out: Vec<PyObject> = Vec::new();
    let iter = r.iter()?;
    for item in iter {
        out.push(item?.unbind());
    }
    Ok(out)
}

#[pyfunction]
pub fn elaborate_foralls(py: Python<'_>, e: PyObject) -> PyResult<PyObject> {
    let b = e.bind(py);
    // Trivial / pass-through cases.
    if b.downcast::<SLiteral>().is_ok()
        || b.downcast::<SHole>().is_ok()
        || b.downcast::<SVar>().is_ok()
        || b.downcast::<SAnnotation>().is_ok()
        || b.downcast::<SAbstraction>().is_ok()
        || b.downcast::<SApplication>().is_ok()
        || b.downcast::<SLet>().is_ok()
        || b.downcast::<SIf>().is_ok()
        || b.downcast::<STypeApplication>().is_ok()
        || b.downcast::<STypeAbstraction>().is_ok()
        || b.downcast::<SRefinementAbstraction>().is_ok()
        || b.downcast::<SRefinementApplication>().is_ok()
    {
        return Ok(e);
    }

    if let Ok(sr) = b.downcast::<SRec>() {
        let sr_ref = sr.borrow();
        let var_name = sr_ref.var_name.clone_ref(py);
        let var_type = sr_ref.var_type.clone_ref(py);
        let var_value = sr_ref.var_value.clone_ref(py);
        let body = sr_ref.body.clone_ref(py);
        let decreasing_by = sr_ref.decreasing_by.clone_ref(py);
        let loc = sr_ref.loc.clone_ref(py);
        let mult = sr_ref.multiplicity.clone_ref(py);
        drop(sr_ref);

        let tvars = get_type_vars(py, &var_type)?;
        if tvars.is_empty() {
            return Ok(e);
        }
        let mut nt = var_type;
        let mut nv = var_value;
        let kind = mk_base_kind(py)?;
        for tv in tvars {
            // tv is an STypeVar; grab its name.
            let tv_b = tv.bind(py);
            let name: Py<Name> = if let Ok(stv) = tv_b.downcast::<STypeVar>() {
                stv.borrow().name.clone_ref(py)
            } else {
                return Err(pyo3::exceptions::PyAssertionError::new_err(
                    "get_type_vars returned non-STypeVar",
                ));
            };
            nt = Py::new(
                py,
                (
                    STypePolymorphism {
                        name: name.clone_ref(py),
                        kind: kind.clone_ref(py),
                        body: nt,
                        loc: default_location(py),
                    },
                    SType,
                ),
            )?
            .into_any();
            nv = Py::new(
                py,
                (
                    STypeAbstraction {
                        name,
                        kind: kind.clone_ref(py),
                        body: nv,
                        loc: default_location(py),
                    },
                    STerm,
                ),
            )?
            .into_any();
        }
        let new_rec = Py::new(
            py,
            (
                SRec {
                    var_name,
                    var_type: nt,
                    var_value: nv,
                    body,
                    decreasing_by,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?;
        return Ok(new_rec.into_any());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Could not elaborate {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

// =============================================================================
// unify
// =============================================================================

/// Bidirectional unification. Mutates `UnificationVar.upper`/`.lower` in
/// place. Returns the list of refined `nty`s produced when unifying a
/// `STypePolymorphism` on the subtype side (the Python returns these so the
/// caller can wrap them with `STypeApplication`).
fn unify(
    py: Python<'_>,
    ctx: &ElaborationTypingContext,
    sub: PyObject,
    sup: PyObject,
) -> PyResult<Vec<PyObject>> {
    let sub_b = sub.bind(py);
    let sup_b = sup.bind(py);

    // (_, Top) -> []
    if let Ok(stc) = sup_b.downcast::<STypeConstructor>() {
        let stc_r = stc.borrow();
        let n = stc_r.name.borrow(py);
        if n.id == 0 && n.name == "Top" {
            return Ok(Vec::new());
        }
    }

    // (STypeConstructor, STypeConstructor)
    if let Ok(sub_tc) = sub_b.downcast::<STypeConstructor>() {
        if let Ok(sup_tc) = sup_b.downcast::<STypeConstructor>() {
            let sub_tc_r = sub_tc.borrow();
            let sup_tc_r = sup_tc.borrow();
            let sn = sub_tc_r.name.borrow(py);
            let pn = sup_tc_r.name.borrow(py);
            if sn.name != pn.name || sn.id != pn.id {
                drop(sn);
                drop(pn);
                let hole = todo_hole(py)?;
                return Err(raise_api(
                    py,
                    "UnificationSubtypingError",
                    vec![hole, sub.clone_ref(py), sup.clone_ref(py)],
                ));
            }
            drop(sn);
            drop(pn);
            let subargs = sub_tc_r.args.clone_ref(py);
            let supargs = sup_tc_r.args.clone_ref(py);
            drop(sub_tc_r);
            drop(sup_tc_r);
            let sa_b = subargs.bind(py);
            let pa_b = supargs.bind(py);
            if sa_b.len() != pa_b.len() {
                let hole = todo_hole(py)?;
                return Err(raise_api(
                    py,
                    "UnificationSubtypingError",
                    vec![hole, sub.clone_ref(py), sup.clone_ref(py)],
                ));
            }
            let mut rt: Vec<PyObject> = Vec::new();
            for i in 0..sa_b.len() {
                let a = sa_b.get_item(i)?.unbind();
                let b = pa_b.get_item(i)?.unbind();
                let mut sub_res = unify(py, ctx, a, b)?;
                rt.append(&mut sub_res);
            }
            return Ok(rt);
        }
    }

    // (SRefinedType, _)
    if let Ok(srt) = sub_b.downcast::<SRefinedType>() {
        let inner = srt.borrow().type_.clone_ref(py);
        return unify(py, ctx, inner, sup);
    }
    // (_, SRefinedType)
    if let Ok(srt) = sup_b.downcast::<SRefinedType>() {
        let inner = srt.borrow().type_.clone_ref(py);
        return unify(py, ctx, sub, inner);
    }

    // (UnificationVar, _)
    if let Ok(uv) = sub_b.downcast::<UnificationVar>() {
        let uv_ref = uv.borrow();
        uv_ref.upper.bind(py).append(sup.clone_ref(py))?;
        // Iterate over a snapshot of lower so re-entrant unify doesn't
        // disturb iteration.
        let lower = uv_ref.lower.clone_ref(py);
        drop(uv_ref);
        let l_b = lower.bind(py);
        let len = l_b.len();
        for i in 0..len {
            let item = l_b.get_item(i)?.unbind();
            unify(py, ctx, item, sup.clone_ref(py))?;
        }
        return Ok(Vec::new());
    }

    // (_, UnificationVar)
    if let Ok(uv) = sup_b.downcast::<UnificationVar>() {
        let uv_ref = uv.borrow();
        uv_ref.lower.bind(py).append(sub.clone_ref(py))?;
        let upper = uv_ref.upper.clone_ref(py);
        drop(uv_ref);
        let u_b = upper.bind(py);
        let len = u_b.len();
        for i in 0..len {
            let item = u_b.get_item(i)?.unbind();
            unify(py, ctx, sub.clone_ref(py), item)?;
        }
        return Ok(Vec::new());
    }

    // (STypePolymorphism, _)
    if let Ok(stp) = sub_b.downcast::<STypePolymorphism>() {
        let stp_r = stp.borrow();
        let stp_name = stp_r.name.clone_ref(py);
        let stp_body = stp_r.body.clone_ref(py);
        drop(stp_r);
        let fresh = ctx.fresh_typevar(py)?;
        let u = mk_unification_var(py, fresh)?;
        let nty = sugar_type_substitution(py, stp_body, stp_name, u)?;
        let mut rt = unify(py, ctx, nty.clone_ref(py), sup)?;
        let mut result = vec![nty];
        result.append(&mut rt);
        return Ok(result);
    }

    // (_, STypePolymorphism)
    if let Ok(stp) = sup_b.downcast::<STypePolymorphism>() {
        let stp_r = stp.borrow();
        let stp_name = stp_r.name.clone_ref(py);
        let stp_body = stp_r.body.clone_ref(py);
        drop(stp_r);
        let fresh = ctx.fresh_typevar(py)?;
        let u = mk_unification_var(py, fresh)?;
        let substituted = sugar_type_substitution(py, stp_body, stp_name, u)?;
        unify(py, ctx, sub, substituted)?;
        return Ok(Vec::new());
    }

    // (SAbstractionType, SAbstractionType)
    if let Ok(sub_at) = sub_b.downcast::<SAbstractionType>() {
        if let Ok(sup_at) = sup_b.downcast::<SAbstractionType>() {
            let sub_r = sub_at.borrow();
            let sup_r = sup_at.borrow();
            let sub_vtype = sub_r.var_type.clone_ref(py);
            let sub_rtype = sub_r.type_.clone_ref(py);
            let sup_vtype = sup_r.var_type.clone_ref(py);
            let sup_rtype = sup_r.type_.clone_ref(py);
            drop(sub_r);
            drop(sup_r);
            unify(py, ctx, sup_vtype, sub_vtype)?;
            unify(py, ctx, sub_rtype, sup_rtype)?;
            return Ok(Vec::new());
        }
    }

    // (STypeVar, STypeVar)
    if let Ok(sub_tv) = sub_b.downcast::<STypeVar>() {
        if let Ok(sup_tv) = sup_b.downcast::<STypeVar>() {
            let s = sub_tv.borrow();
            let p = sup_tv.borrow();
            let sn = s.name.borrow(py);
            let pn = p.name.borrow(py);
            if sn.name == pn.name && sn.id == pn.id {
                return Ok(Vec::new());
            } else {
                drop(sn);
                drop(pn);
                let hole = todo_hole(py)?;
                return Err(raise_api(
                    py,
                    "UnificationSubtypingError",
                    vec![hole, sub.clone_ref(py), sup.clone_ref(py)],
                ));
            }
        }
    }

    // Fallback.
    let hole = todo_hole(py)?;
    Err(raise_api(
        py,
        "UnificationSubtypingError",
        vec![hole, sub, sup],
    ))
}

// =============================================================================
// unify_single
// =============================================================================

fn is_st_top(py: Python<'_>, ty: &PyObject) -> bool {
    let b = ty.bind(py);
    if let Ok(stc) = b.downcast::<STypeConstructor>() {
        let stc = stc.borrow();
        let n = stc.name.borrow(py);
        n.id == 0 && n.name == "Top"
    } else {
        false
    }
}

fn ty_equal(py: Python<'_>, a: &PyObject, b: &PyObject) -> PyResult<bool> {
    a.bind(py).eq(b.bind(py))
}

fn unify_single(py: Python<'_>, vname: &str, xs: &Py<PyList>) -> PyResult<PyObject> {
    let l = xs.bind(py);
    let mut filtered: Vec<PyObject> = Vec::new();
    for i in 0..l.len() {
        let item = l.get_item(i)?.unbind();
        if !is_st_top(py, &item) {
            filtered.push(item);
        }
    }
    if filtered.is_empty() {
        return st_unit(py);
    }
    let fst = filtered[0].clone_ref(py);
    for snd in filtered.iter().skip(1) {
        if !ty_equal(py, &fst, snd)? {
            return Err(raise_api(
                py,
                "UnificationFailedError",
                vec![
                    pyo3::types::PyString::new_bound(py, vname).into_any().unbind(),
                    fst.clone_ref(py),
                    snd.clone_ref(py),
                ],
            ));
        }
    }
    Ok(fst)
}

// =============================================================================
// remove_unions_and_intersections
// =============================================================================

fn remove_unions_and_intersections(
    py: Python<'_>,
    ctx: &ElaborationTypingContext,
    ty: PyObject,
) -> PyResult<PyObject> {
    let b = ty.bind(py);

    if let Ok(u) = b.downcast::<Union>() {
        let u_ref = u.borrow();
        let united = u_ref.united.clone_ref(py);
        drop(u_ref);
        return unify_single(py, "?", &united);
    }
    if let Ok(i) = b.downcast::<Intersection>() {
        let i_ref = i.borrow();
        let intersected = i_ref.intersected.clone_ref(py);
        drop(i_ref);
        return unify_single(py, "?", &intersected);
    }

    if let Ok(at) = b.downcast::<SAbstractionType>() {
        let r = at.borrow();
        let name = r.var_name.clone_ref(py);
        let vtype = r.var_type.clone_ref(py);
        let rtype = r.type_.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        let mult = r.multiplicity.clone_ref(py);
        drop(r);
        let new_vtype = remove_unions_and_intersections(py, ctx, vtype)?;
        let new_rtype = remove_unions_and_intersections(py, ctx, rtype)?;
        return Ok(Py::new(
            py,
            (
                SAbstractionType {
                    var_name: name,
                    var_type: new_vtype,
                    type_: new_rtype,
                    loc,
                    multiplicity: mult,
                },
                SType,
            ),
        )?
        .into_any());
    }

    if let Ok(tp) = b.downcast::<STypePolymorphism>() {
        let r = tp.borrow();
        let name = r.name.clone_ref(py);
        let kind = r.kind.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_body = remove_unions_and_intersections(py, ctx, body)?;
        return Ok(Py::new(
            py,
            (
                STypePolymorphism { name, kind, body: new_body, loc },
                SType,
            ),
        )?
        .into_any());
    }

    if let Ok(rp) = b.downcast::<SRefinementPolymorphism>() {
        let r = rp.borrow();
        let name = r.name.clone_ref(py);
        let sort = r.sort.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_sort = remove_unions_and_intersections(py, ctx, sort)?;
        let new_body = remove_unions_and_intersections(py, ctx, body)?;
        return Ok(Py::new(
            py,
            (
                SRefinementPolymorphism { name, sort: new_sort, body: new_body, loc },
                SType,
            ),
        )?
        .into_any());
    }

    if let Ok(tc) = b.downcast::<STypeConstructor>() {
        let r = tc.borrow();
        let name = r.name.clone_ref(py);
        let args = r.args.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_args = PyList::empty_bound(py);
        let a_b = args.bind(py);
        for i in 0..a_b.len() {
            let item = a_b.get_item(i)?.unbind();
            new_args.append(remove_unions_and_intersections(py, ctx, item)?)?;
        }
        return Ok(Py::new(
            py,
            (
                STypeConstructor { name, args: new_args.unbind(), loc },
                SType,
            ),
        )?
        .into_any());
    }

    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let r = rt.borrow();
        let name = r.name.clone_ref(py);
        let ity = r.type_.clone_ref(py);
        let refn = r.refinement.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_ity = remove_unions_and_intersections(py, ctx, ity)?;
        return Ok(Py::new(
            py,
            (
                SRefinedType { name, type_: new_ity, refinement: refn, loc },
                SType,
            ),
        )?
        .into_any());
    }

    Ok(ty)
}

// =============================================================================
// wrap_unification / ensure_not_polymorphism
// =============================================================================

#[allow(dead_code)]
fn wrap_unification(
    py: Python<'_>,
    _ctx: &ElaborationTypingContext,
    t: PyObject,
    us: Vec<PyObject>,
) -> PyResult<PyObject> {
    let mut nt = t;
    for u in us {
        nt = mk_type_app(py, nt, u)?;
    }
    Ok(nt)
}

#[allow(dead_code)]
fn ensure_not_polymorphism(
    py: Python<'_>,
    ctx: &ElaborationTypingContext,
    mut t: PyObject,
    mut ty: PyObject,
) -> PyResult<(PyObject, PyObject)> {
    loop {
        let ty_b = ty.bind(py);
        if let Ok(stp) = ty_b.downcast::<STypePolymorphism>() {
            let r = stp.borrow();
            let name = r.name.clone_ref(py);
            let body = r.body.clone_ref(py);
            drop(r);
            let fresh = ctx.fresh_typevar(py)?;
            let u = mk_unification_var(py, fresh)?;
            ty = sugar_type_substitution(py, body, name, u.clone_ref(py))?;
            t = mk_type_app(py, t, u)?;
        } else {
            break;
        }
    }
    Ok((t, ty))
}

// =============================================================================
// elaborate_synth / elaborate_check / get_rid_of_polymorphism
// =============================================================================

fn elaborate_synth(
    py: Python<'_>,
    ctx: &ElaborationTypingContext,
    t: PyObject,
) -> PyResult<(PyObject, PyObject)> {
    let b = t.bind(py);

    if let Ok(slit) = b.downcast::<SLiteral>() {
        let ty = slit.borrow().type_.clone_ref(py);
        return Ok((t, ty));
    }
    if let Ok(sv) = b.downcast::<SVar>() {
        let name = sv.borrow().name.clone_ref(py);
        let ty = ctx.type_of(py, name)?;
        if ty.bind(py).is_none() {
            return Err(raise_api(
                py,
                "UnificationUnknownTypeError",
                vec![t.clone_ref(py)],
            ));
        }
        return Ok((t, ty));
    }
    if b.downcast::<SAnonConstructor>().is_ok() {
        return Err(raise_api(
            py,
            "UnificationUnknownTypeError",
            vec![t.clone_ref(py)],
        ));
    }
    if b.downcast::<SHole>().is_ok() {
        let fresh = ctx.fresh_typevar(py)?;
        let u = mk_unification_var(py, fresh)?;
        return Ok((t, u));
    }
    if let Ok(sa) = b.downcast::<SAnnotation>() {
        let r = sa.borrow();
        let expr = r.expr.clone_ref(py);
        let ty = r.type_.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let ann = elaborate_check(py, ctx, expr, ty.clone_ref(py))?;
        let new_ann = Py::new(
            py,
            (
                SAnnotation { expr: ann, type_: ty.clone_ref(py), loc },
                STerm,
            ),
        )?
        .into_any();
        return Ok((new_ann, ty));
    }
    if let Ok(sab) = b.downcast::<SAbstraction>() {
        let r = sab.borrow();
        let name = r.var_name.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let fresh = ctx.fresh_typevar(py)?;
        let u = mk_unification_var(py, fresh)?;
        let nctx = ctx.with_var(py, name.clone_ref(py), u.clone_ref(py))?;
        let (t2, bt) = elaborate_synth(py, &nctx, body)?;
        let new_abs = Py::new(
            py,
            (
                SAbstraction { var_name: name.clone_ref(py), body: t2, loc },
                STerm,
            ),
        )?
        .into_any();
        let abs_ty = Py::new(
            py,
            (
                SAbstractionType {
                    var_name: name,
                    var_type: u,
                    type_: bt,
                    loc: default_location(py),
                    multiplicity: crate::types::default_multiplicity(py),
                },
                SType,
            ),
        )?
        .into_any();
        return Ok((new_abs, abs_ty));
    }
    if let Ok(sta) = b.downcast::<STypeApplication>() {
        let r = sta.borrow();
        let body = r.body.clone_ref(py);
        let ty_field = r.type_.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let (inner, innert) = elaborate_synth(py, ctx, body)?;
        // assert innert is STypePolymorphism
        let innert_b = innert.bind(py);
        let stp = innert_b.downcast::<STypePolymorphism>().map_err(|_| {
            pyo3::exceptions::PyAssertionError::new_err(
                "expected STypePolymorphism in STypeApplication synth",
            )
        })?;
        let stp_r = stp.borrow();
        let stp_name = stp_r.name.clone_ref(py);
        let stp_body = stp_r.body.clone_ref(py);
        drop(stp_r);
        // Create fresh u with upper/lower seeded with ty_field.
        let fresh = ctx.fresh_typevar(py)?;
        let upper = PyList::empty_bound(py);
        upper.append(ty_field.clone_ref(py))?;
        let lower = PyList::empty_bound(py);
        lower.append(ty_field.clone_ref(py))?;
        let u = Py::new(
            py,
            (
                UnificationVar {
                    name: fresh,
                    lower: lower.unbind(),
                    upper: upper.unbind(),
                    loc: default_location(py),
                },
                SType,
            ),
        )?
        .into_any();
        let nty = sugar_type_substitution(py, stp_body, stp_name, u)?;
        let new_app = Py::new(
            py,
            (
                STypeApplication { body: inner, type_: ty_field, loc },
                STerm,
            ),
        )?
        .into_any();
        return Ok((new_app, nty));
    }
    if let Ok(sra) = b.downcast::<SRefinementApplication>() {
        let r = sra.borrow();
        let body = r.body.clone_ref(py);
        let refinement = r.refinement.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let (inner, innert) = elaborate_synth(py, ctx, body)?;
        let innert_b = innert.bind(py);
        let srp = innert_b.downcast::<SRefinementPolymorphism>().map_err(|_| {
            pyo3::exceptions::PyAssertionError::new_err(
                "expected SRefinementPolymorphism in SRefinementApplication synth",
            )
        })?;
        let srp_r = srp.borrow();
        let srp_name = srp_r.name.clone_ref(py);
        let srp_sort = srp_r.sort.clone_ref(py);
        let srp_body = srp_r.body.clone_ref(py);
        drop(srp_r);
        let under_name = fresh_named(py, "_")?;
        let bool_ty = st_bool(py)?;
        let ref_type = Py::new(
            py,
            (
                SAbstractionType {
                    var_name: under_name,
                    var_type: srp_sort,
                    type_: bool_ty,
                    loc: default_location(py),
                    multiplicity: crate::types::default_multiplicity(py),
                },
                SType,
            ),
        )?
        .into_any();
        let nrefinement = elaborate_check(py, ctx, refinement, ref_type)?;
        let nty =
            substitution_sterm_in_stype(py, srp_body, nrefinement.clone_ref(py), srp_name)?;
        let new_app = Py::new(
            py,
            (
                SRefinementApplication {
                    body: inner,
                    refinement: nrefinement,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any();
        return Ok((new_app, nty));
    }
    if let Ok(sl) = b.downcast::<SLet>() {
        let r = sl.borrow();
        let name = r.var_name.clone_ref(py);
        let value = r.var_value.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        let mult = r.multiplicity.clone_ref(py);
        drop(r);
        let fresh = ctx.fresh_typevar(py)?;
        let u = mk_unification_var(py, fresh)?;
        let nval = elaborate_check(py, ctx, value, u.clone_ref(py))?;
        let nctx = ctx.with_var(py, name.clone_ref(py), u)?;
        let (nbody, nbody_type) = elaborate_synth(py, &nctx, body)?;
        let new_let = Py::new(
            py,
            (
                SLet {
                    var_name: name,
                    var_value: nval,
                    body: nbody,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any();
        return Ok((new_let, nbody_type));
    }
    if let Ok(sr) = b.downcast::<SRec>() {
        let r = sr.borrow();
        let name = r.var_name.clone_ref(py);
        let vty = r.var_type.clone_ref(py);
        let val = r.var_value.clone_ref(py);
        let body = r.body.clone_ref(py);
        let decreasing_by = r.decreasing_by.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        let mult = r.multiplicity.clone_ref(py);
        drop(r);
        let nctx = ctx.with_var(py, name.clone_ref(py), vty.clone_ref(py))?;
        let nval = elaborate_check(py, &nctx, val, vty.clone_ref(py))?;
        let (nbody, nbody_type) = elaborate_synth(py, &nctx, body)?;
        let new_rec = Py::new(
            py,
            (
                SRec {
                    var_name: name,
                    var_type: vty,
                    var_value: nval,
                    body: nbody,
                    decreasing_by,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any();
        return Ok((new_rec, nbody_type));
    }
    if let Ok(sif) = b.downcast::<SIf>() {
        let r = sif.borrow();
        let cond = r.cond.clone_ref(py);
        let then = r.then.clone_ref(py);
        let otherwise = r.otherwise.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let ncond = elaborate_check(py, ctx, cond, st_bool(py)?)?;
        let (nthen, nthen_type) = elaborate_synth(py, ctx, then)?;
        let (nelse, nelse_type) = elaborate_synth(py, ctx, otherwise)?;
        let fresh = ctx.fresh_typevar(py)?;
        let u = mk_unification_var(py, fresh)?;
        unify(py, ctx, nthen_type, u.clone_ref(py))?;
        unify(py, ctx, nelse_type, u.clone_ref(py))?;
        let new_if = Py::new(
            py,
            (
                SIf {
                    cond: ncond,
                    then: nthen,
                    otherwise: nelse,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any();
        return Ok((new_if, u));
    }
    if let Ok(sap) = b.downcast::<SApplication>() {
        let r = sap.borrow();
        let fun = r.fun.clone_ref(py);
        let arg = r.arg.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let (mut nfun, mut nfun_type) = elaborate_synth(py, ctx, fun)?;
        // Peel STypePolymorphism
        loop {
            let t_b = nfun_type.bind(py);
            if let Ok(stp) = t_b.downcast::<STypePolymorphism>() {
                let stp_r = stp.borrow();
                let n = stp_r.name.clone_ref(py);
                let body = stp_r.body.clone_ref(py);
                drop(stp_r);
                let fresh = ctx.fresh_typevar(py)?;
                let u = mk_unification_var(py, fresh)?;
                nfun = mk_type_app(py, nfun, u.clone_ref(py))?;
                nfun_type = sugar_type_substitution(py, body, n, u)?;
            } else {
                break;
            }
        }
        // Peel SRefinementPolymorphism
        loop {
            let t_b = nfun_type.bind(py);
            if let Ok(srp) = t_b.downcast::<SRefinementPolymorphism>() {
                let srp_r = srp.borrow();
                let n = srp_r.name.clone_ref(py);
                let body = srp_r.body.clone_ref(py);
                drop(srp_r);
                let h_name = fresh_named(py, "_pred")?;
                let h = Py::new(
                    py,
                    (
                        SHole { name: h_name, loc: default_location(py) },
                        STerm,
                    ),
                )?
                .into_any();
                nfun = Py::new(
                    py,
                    (
                        SRefinementApplication {
                            body: nfun,
                            refinement: h.clone_ref(py),
                            loc: default_location(py),
                        },
                        STerm,
                    ),
                )?
                .into_any();
                nfun_type = substitution_sterm_in_stype(py, body, h, n)?;
            } else {
                break;
            }
        }
        // Match against SAbstractionType
        let nfun_type_b = nfun_type.bind(py);
        if let Ok(at) = nfun_type_b.downcast::<SAbstractionType>() {
            let at_r = at.borrow();
            let arg_type = at_r.var_type.clone_ref(py);
            let return_type = at_r.type_.clone_ref(py);
            drop(at_r);
            let narg = elaborate_check(py, ctx, arg, arg_type)?;
            let new_app = Py::new(
                py,
                (
                    SApplication { fun: nfun, arg: narg, loc },
                    STerm,
                ),
            )?
            .into_any();
            return Ok((new_app, return_type));
        }
        return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "Expected an abstraction type, but got {} for {}.",
            nfun_type.bind(py).str()?,
            nfun.bind(py).str()?
        )));
    }
    Err(raise_api(
        py,
        "UnificationUnknownTypeError",
        vec![t.clone_ref(py)],
    ))
}

fn elaborate_check(
    py: Python<'_>,
    ctx: &ElaborationTypingContext,
    t: PyObject,
    ty: PyObject,
) -> PyResult<PyObject> {
    let t_b = t.bind(py);
    let ty_b = ty.bind(py);

    // (SAbstraction, SAbstractionType)
    if let Ok(sab) = t_b.downcast::<SAbstraction>() {
        if let Ok(at) = ty_b.downcast::<SAbstractionType>() {
            let sab_r = sab.borrow();
            let name = sab_r.var_name.clone_ref(py);
            let body = sab_r.body.clone_ref(py);
            let loc = sab_r.loc.clone_ref(py);
            drop(sab_r);
            let at_r = at.borrow();
            let aname = at_r.var_name.clone_ref(py);
            let aty = at_r.var_type.clone_ref(py);
            let rty = at_r.type_.clone_ref(py);
            drop(at_r);
            let nctx = ctx.with_var(py, name.clone_ref(py), aty)?;
            let svar = Py::new(
                py,
                (
                    SVar { name: name.clone_ref(py), loc: default_location(py) },
                    STerm,
                ),
            )?
            .into_any();
            let new_rty = substitution_sterm_in_stype(py, rty, svar, aname)?;
            let nbody = elaborate_check(py, &nctx, body, new_rty)?;
            let new_abs = Py::new(
                py,
                (
                    SAbstraction { var_name: name, body: nbody, loc },
                    STerm,
                ),
            )?
            .into_any();
            return Ok(new_abs);
        }
    }

    // (SLet, _)
    if let Ok(sl) = t_b.downcast::<SLet>() {
        let r = sl.borrow();
        let name = r.var_name.clone_ref(py);
        let val = r.var_value.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        let mult = r.multiplicity.clone_ref(py);
        drop(r);
        let fresh = ctx.fresh_typevar(py)?;
        let u = mk_unification_var(py, fresh)?;
        let nval = elaborate_check(py, ctx, val, u.clone_ref(py))?;
        let nctx = ctx.with_var(py, name.clone_ref(py), u)?;
        let nbody = elaborate_check(py, &nctx, body, ty)?;
        let new_let = Py::new(
            py,
            (
                SLet {
                    var_name: name,
                    var_value: nval,
                    body: nbody,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any();
        return Ok(new_let);
    }

    // (SRec, _)
    if let Ok(sr) = t_b.downcast::<SRec>() {
        let r = sr.borrow();
        let name = r.var_name.clone_ref(py);
        let vty = r.var_type.clone_ref(py);
        let val = r.var_value.clone_ref(py);
        let body = r.body.clone_ref(py);
        let decreasing_by = r.decreasing_by.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        let mult = r.multiplicity.clone_ref(py);
        drop(r);
        let nctx = ctx.with_var(py, name.clone_ref(py), vty.clone_ref(py))?;
        let nval = elaborate_check(py, &nctx, val, vty.clone_ref(py))?;
        let nbody = elaborate_check(py, &nctx, body, ty)?;
        let new_rec = Py::new(
            py,
            (
                SRec {
                    var_name: name,
                    var_type: vty,
                    var_value: nval,
                    body: nbody,
                    decreasing_by,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any();
        return Ok(new_rec);
    }

    // (SIf, _)
    if let Ok(sif) = t_b.downcast::<SIf>() {
        let r = sif.borrow();
        let cond = r.cond.clone_ref(py);
        let then = r.then.clone_ref(py);
        let otherwise = r.otherwise.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let ncond = elaborate_check(py, ctx, cond, st_bool(py)?)?;
        let nthen = elaborate_check(py, ctx, then, ty.clone_ref(py))?;
        let nelse = elaborate_check(py, ctx, otherwise, ty)?;
        let new_if = Py::new(
            py,
            (
                SIf {
                    cond: ncond,
                    then: nthen,
                    otherwise: nelse,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any();
        return Ok(new_if);
    }

    // (STypeAbstraction, STypePolymorphism)
    if let Ok(sta) = t_b.downcast::<STypeAbstraction>() {
        if let Ok(stp) = ty_b.downcast::<STypePolymorphism>() {
            let sta_r = sta.borrow();
            let name = sta_r.name.clone_ref(py);
            let kind = sta_r.kind.clone_ref(py);
            let body = sta_r.body.clone_ref(py);
            let loc = sta_r.loc.clone_ref(py);
            drop(sta_r);
            let stp_r = stp.borrow();
            let tname = stp_r.name.clone_ref(py);
            let tbody = stp_r.body.clone_ref(py);
            drop(stp_r);
            // assert UnificationKindError side-effect-only — Python's
            // `assert UnificationKindError(...)` constructs but doesn't raise.
            // We mirror that by skipping.
            let nctx = ctx.with_typevar(py, name.clone_ref(py), kind.clone_ref(py))?;
            let stv = Py::new(
                py,
                (
                    STypeVar { name: name.clone_ref(py), loc: default_location(py) },
                    SType,
                ),
            )?
            .into_any();
            let nty = sugar_type_substitution(py, tbody, tname, stv)?;
            let nbody = elaborate_check(py, &nctx, body, nty)?;
            let new_abs = Py::new(
                py,
                (
                    STypeAbstraction { name, kind, body: nbody, loc },
                    STerm,
                ),
            )?
            .into_any();
            return Ok(new_abs);
        }
    }

    // (SRefinementAbstraction, SRefinementPolymorphism)
    if let Ok(sra) = t_b.downcast::<SRefinementAbstraction>() {
        if let Ok(srp) = ty_b.downcast::<SRefinementPolymorphism>() {
            let sra_r = sra.borrow();
            let pname = sra_r.name.clone_ref(py);
            let sort = sra_r.sort.clone_ref(py);
            let body = sra_r.body.clone_ref(py);
            let loc = sra_r.loc.clone_ref(py);
            drop(sra_r);
            let srp_r = srp.borrow();
            let rname = srp_r.name.clone_ref(py);
            let rsort = srp_r.sort.clone_ref(py);
            let tbody = srp_r.body.clone_ref(py);
            drop(srp_r);
            unify(py, ctx, sort.clone_ref(py), rsort)?;
            let nty = substitute_refinement_param_in_stype(py, tbody, rname, pname.clone_ref(py))?;
            let nbody = elaborate_check(py, ctx, body, nty)?;
            let new_abs = Py::new(
                py,
                (
                    SRefinementAbstraction {
                        name: pname,
                        sort,
                        body: nbody,
                        loc,
                    },
                    STerm,
                ),
            )?
            .into_any();
            return Ok(new_abs);
        }
    }

    // (SAbstraction, SRefinementPolymorphism)
    if let Ok(_sab) = t_b.downcast::<SAbstraction>() {
        if let Ok(srp) = ty_b.downcast::<SRefinementPolymorphism>() {
            let r = srp.borrow();
            let rname = r.name.clone_ref(py);
            let rsort = r.sort.clone_ref(py);
            let tbody = r.body.clone_ref(py);
            drop(r);
            // grab loc from SAbstraction t
            let sab2 = t_b.downcast::<SAbstraction>().unwrap();
            let loc = sab2.borrow().loc.clone_ref(py);
            let nbody = elaborate_check(py, ctx, t.clone_ref(py), tbody)?;
            let new_abs = Py::new(
                py,
                (
                    SRefinementAbstraction {
                        name: rname,
                        sort: rsort,
                        body: nbody,
                        loc,
                    },
                    STerm,
                ),
            )?
            .into_any();
            return Ok(new_abs);
        }
    }

    // (SAnonConstructor, _)
    if let Ok(sac) = t_b.downcast::<SAnonConstructor>() {
        let r = sac.borrow();
        let cname = r.name.clone();
        let loc = r.loc.clone_ref(py);
        drop(r);
        let base_name = extract_base_type_name(py, &ty)?;
        let ctor_to_type = ctx.constructor_to_type.bind(py);
        let ctor_defs = ctx.constructor_defs.bind(py);
        let cname_pystr = pyo3::types::PyString::new_bound(py, &cname);

        if let Some(bname) = base_name.as_ref() {
            let in_to_type = ctor_to_type.contains(&cname_pystr)?;
            let in_defs = ctor_defs.contains(&cname_pystr)?;
            if in_to_type && in_defs {
                let mapped = ctor_to_type.get_item(&cname_pystr)?.unwrap();
                let expected_name_obj = mapped.getattr("name")?;
                let expected_name: String = expected_name_obj.extract()?;
                if &expected_name == bname {
                    let resolved_name_obj = ctor_defs.get_item(&cname_pystr)?.unwrap();
                    let resolved_name: Py<Name> =
                        resolved_name_obj.downcast::<Name>()?.clone().unbind();
                    let resolved = Py::new(
                        py,
                        (
                            SVar { name: resolved_name, loc },
                            STerm,
                        ),
                    )?
                    .into_any();
                    return elaborate_check(py, ctx, resolved, ty);
                }
            }
        }
        if ctor_defs.contains(&cname_pystr)? {
            let resolved_name_obj = ctor_defs.get_item(&cname_pystr)?.unwrap();
            let resolved_name: Py<Name> = resolved_name_obj.downcast::<Name>()?.clone().unbind();
            let resolved = Py::new(
                py,
                (
                    SVar { name: resolved_name, loc },
                    STerm,
                ),
            )?
            .into_any();
            return elaborate_check(py, ctx, resolved, ty);
        }
        return Err(raise_api(
            py,
            "UnificationUnknownTypeError",
            vec![t.clone_ref(py)],
        ));
    }

    // (SApplication, _)
    if let Ok(sap) = t_b.downcast::<SApplication>() {
        let r = sap.borrow();
        let fun = r.fun.clone_ref(py);
        let arg = r.arg.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let fresh = ctx.fresh_typevar(py)?;
        let u = mk_unification_var(py, fresh)?;
        let under_name = fresh_named(py, "_")?;
        let abs_ty = Py::new(
            py,
            (
                SAbstractionType {
                    var_name: under_name,
                    var_type: u.clone_ref(py),
                    type_: ty,
                    loc: default_location(py),
                    multiplicity: crate::types::default_multiplicity(py),
                },
                SType,
            ),
        )?
        .into_any();
        let nfun = elaborate_check(py, ctx, fun, abs_ty)?;
        let narg = elaborate_check(py, ctx, arg, u)?;
        let new_app = Py::new(
            py,
            (
                SApplication { fun: nfun, arg: narg, loc },
                STerm,
            ),
        )?
        .into_any();
        return Ok(new_app);
    }

    // Fallback: synth + unify
    let (c, s) = elaborate_synth(py, ctx, t)?;
    let (c, s) = get_rid_of_polymorphism(py, ctx, c, s, ty.clone_ref(py))?;
    unify(py, ctx, s, ty)?;
    Ok(c)
}

fn get_rid_of_polymorphism(
    py: Python<'_>,
    ctx: &ElaborationTypingContext,
    mut c: PyObject,
    mut s: PyObject,
    ty: PyObject,
) -> PyResult<(PyObject, PyObject)> {
    loop {
        let s_b = s.bind(py);
        let ty_b = ty.bind(py);
        let s_is_stp = s_b.downcast::<STypePolymorphism>().is_ok();
        let ty_is_stp = ty_b.downcast::<STypePolymorphism>().is_ok();
        if s_is_stp && !ty_is_stp {
            let stp = s_b.downcast::<STypePolymorphism>().unwrap();
            let stp_r = stp.borrow();
            let n = stp_r.name.clone_ref(py);
            let body = stp_r.body.clone_ref(py);
            drop(stp_r);
            let fresh = ctx.fresh_typevar(py)?;
            let u = mk_unification_var(py, fresh)?;
            c = mk_type_app(py, c, u.clone_ref(py))?;
            s = sugar_type_substitution(py, body, n, u)?;
        } else {
            break;
        }
    }
    loop {
        let s_b = s.bind(py);
        let ty_b = ty.bind(py);
        let s_is_srp = s_b.downcast::<SRefinementPolymorphism>().is_ok();
        let ty_is_srp = ty_b.downcast::<SRefinementPolymorphism>().is_ok();
        if s_is_srp && !ty_is_srp {
            let srp = s_b.downcast::<SRefinementPolymorphism>().unwrap();
            let srp_r = srp.borrow();
            let n = srp_r.name.clone_ref(py);
            let body = srp_r.body.clone_ref(py);
            drop(srp_r);
            let h_name = fresh_named(py, "_pred")?;
            let h = Py::new(
                py,
                (
                    SHole { name: h_name, loc: default_location(py) },
                    STerm,
                ),
            )?
            .into_any();
            c = Py::new(
                py,
                (
                    SRefinementApplication {
                        body: c,
                        refinement: h.clone_ref(py),
                        loc: default_location(py),
                    },
                    STerm,
                ),
            )?
            .into_any();
            s = substitution_sterm_in_stype(py, body, h, n)?;
        } else {
            break;
        }
    }
    Ok((c, s))
}

// =============================================================================
// extract_direction / replace_unification_variables /
// remove_from_union_and_intersection / handle_unification_in_type
// =============================================================================

fn extract_direction_into(
    py: Python<'_>,
    ty: &PyObject,
    out: &Bound<'_, pyo3::types::PySet>,
) -> PyResult<()> {
    let b = ty.bind(py);
    if let Ok(uv) = b.downcast::<UnificationVar>() {
        let uv_r = uv.borrow();
        let lower = uv_r.lower.clone_ref(py);
        let upper = uv_r.upper.clone_ref(py);
        drop(uv_r);
        let l_b = lower.bind(py);
        for i in 0..l_b.len() {
            let item = l_b.get_item(i)?.unbind();
            extract_direction_into(py, &item, out)?;
        }
        let u_b = upper.bind(py);
        for i in 0..u_b.len() {
            let item = u_b.get_item(i)?.unbind();
            extract_direction_into(py, &item, out)?;
        }
        return Ok(());
    }
    out.add(ty.clone_ref(py))?;
    Ok(())
}

fn extract_direction_as_list(py: Python<'_>, ty: &PyObject) -> PyResult<Py<PyList>> {
    let set = pyo3::types::PySet::empty_bound(py)?;
    extract_direction_into(py, ty, &set)?;
    let out = PyList::empty_bound(py);
    for item in set.iter() {
        out.append(item)?;
    }
    Ok(out.unbind())
}

fn replace_unification_variables(
    py: Python<'_>,
    _ctx: &ElaborationTypingContext,
    ty: PyObject,
) -> PyResult<(PyObject, Vec<PyObject>, Vec<PyObject>)> {
    // We don't actually fill unions/intersections in `go` (Python doesn't
    // either — both lists stay empty), but the algorithm refers to them via
    // identity through replacement walks; since the Python `go` only creates
    // `Union(extract_direction(...))` and never appends to the local
    // `unions`/`intersections`, we mirror that here. However, after the call
    // we collect *all* the Union nodes we *created* by traversal and return
    // them so the polar-removal pass can mutate them.
    //
    // To make the polar pass work correctly we need to collect *both* the
    // Union nodes we create AND the (empty) intersection nodes. We do that
    // by threading a mutable Vec through the recursion.
    let mut unions: Vec<PyObject> = Vec::new();
    let mut intersections: Vec<PyObject> = Vec::new();
    let new_ty = replace_uv_go(py, ty, true, &mut unions, &mut intersections)?;
    Ok((new_ty, unions, intersections))
}

fn replace_uv_go(
    py: Python<'_>,
    ty: PyObject,
    polarity: bool,
    unions: &mut Vec<PyObject>,
    intersections: &mut Vec<PyObject>,
) -> PyResult<PyObject> {
    let b = ty.bind(py);
    if b.downcast::<STypeVar>().is_ok() {
        return Ok(ty);
    }
    if let Ok(at) = b.downcast::<SAbstractionType>() {
        let r = at.borrow();
        let name = r.var_name.clone_ref(py);
        let vty = r.var_type.clone_ref(py);
        let rty = r.type_.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        let mult = r.multiplicity.clone_ref(py);
        drop(r);
        let new_vty = replace_uv_go(py, vty, !polarity, unions, intersections)?;
        let new_rty = replace_uv_go(py, rty, polarity, unions, intersections)?;
        return Ok(Py::new(
            py,
            (
                SAbstractionType {
                    var_name: name,
                    var_type: new_vty,
                    type_: new_rty,
                    loc,
                    multiplicity: mult,
                },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let r = rt.borrow();
        let name = r.name.clone_ref(py);
        let ity = r.type_.clone_ref(py);
        let refn = r.refinement.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_ity = replace_uv_go(py, ity, polarity, unions, intersections)?;
        return Ok(Py::new(
            py,
            (
                SRefinedType { name, type_: new_ity, refinement: refn, loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(tp) = b.downcast::<STypePolymorphism>() {
        let r = tp.borrow();
        let name = r.name.clone_ref(py);
        let kind = r.kind.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_body = replace_uv_go(py, body, polarity, unions, intersections)?;
        return Ok(Py::new(
            py,
            (
                STypePolymorphism { name, kind, body: new_body, loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(rp) = b.downcast::<SRefinementPolymorphism>() {
        let r = rp.borrow();
        let name = r.name.clone_ref(py);
        let sort = r.sort.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_sort = replace_uv_go(py, sort, polarity, unions, intersections)?;
        let new_body = replace_uv_go(py, body, polarity, unions, intersections)?;
        return Ok(Py::new(
            py,
            (
                SRefinementPolymorphism { name, sort: new_sort, body: new_body, loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(tc) = b.downcast::<STypeConstructor>() {
        let r = tc.borrow();
        let name = r.name.clone_ref(py);
        let args = r.args.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let a_b = args.bind(py);
        let new_args = PyList::empty_bound(py);
        for i in 0..a_b.len() {
            let item = a_b.get_item(i)?.unbind();
            new_args.append(replace_uv_go(py, item, polarity, unions, intersections)?)?;
        }
        return Ok(Py::new(
            py,
            (
                STypeConstructor { name, args: new_args.unbind(), loc },
                SType,
            ),
        )?
        .into_any());
    }
    if b.downcast::<UnificationVar>().is_ok() {
        let direction = extract_direction_as_list(py, &ty)?;
        let u = Py::new(
            py,
            (
                Union {
                    united: direction,
                    loc: default_location(py),
                },
                SType,
            ),
        )?
        .into_any();
        // Mirror the Python: the local `unions` / `intersections` lists in
        // replace_unification_variables are intentionally never populated by
        // `go`. The polar-removal pass over them is therefore a no-op; the
        // collapsing happens in `remove_unions_and_intersections`.
        let _ = unions;
        let _ = intersections;
        return Ok(u);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "replace_unification_variables: unhandled type {}",
        b.str()?
    )))
}

fn name_in(py: Python<'_>, names: &[Py<Name>], target: &Py<Name>) -> bool {
    let t = target.borrow(py);
    for n in names {
        let nn = n.borrow(py);
        if nn.name == t.name && nn.id == t.id {
            return true;
        }
    }
    false
}

fn remove_from_union_and_intersection(
    py: Python<'_>,
    unions: &[PyObject],
    intersections: &[PyObject],
    to_be_removed: &[Py<Name>],
) -> PyResult<()> {
    let rem = |x: &PyObject| -> PyResult<bool> {
        let b = x.bind(py);
        if let Ok(uv) = b.downcast::<UnificationVar>() {
            let uv_r = uv.borrow();
            let name = uv_r.name.clone_ref(py);
            drop(uv_r);
            Ok(!name_in(py, to_be_removed, &name))
        } else {
            Ok(true)
        }
    };

    for i in intersections {
        let b = i.bind(py);
        let inter = b.downcast::<Intersection>().map_err(|_| {
            pyo3::exceptions::PyAssertionError::new_err("expected Intersection")
        })?;
        let inter_r = inter.borrow();
        let lst = inter_r.intersected.clone_ref(py);
        drop(inter_r);
        let l_b = lst.bind(py);
        let new_list = PyList::empty_bound(py);
        for k in 0..l_b.len() {
            let item = l_b.get_item(k)?.unbind();
            if rem(&item)? {
                new_list.append(item)?;
            }
        }
        // Mutate the Intersection's `intersected` field.
        let inter_r2 = inter.borrow();
        inter_r2.intersected.bind(py).call_method0("clear")?;
        for k in 0..new_list.len() {
            inter_r2.intersected.bind(py).append(new_list.get_item(k)?)?;
        }
    }

    for u in unions {
        let b = u.bind(py);
        let un = b.downcast::<Union>().map_err(|_| {
            pyo3::exceptions::PyAssertionError::new_err("expected Union")
        })?;
        let un_r = un.borrow();
        let lst = un_r.united.clone_ref(py);
        drop(un_r);
        let l_b = lst.bind(py);
        let new_list = PyList::empty_bound(py);
        for k in 0..l_b.len() {
            let item = l_b.get_item(k)?.unbind();
            if rem(&item)? {
                new_list.append(item)?;
            }
        }
        let un_r2 = un.borrow();
        un_r2.united.bind(py).call_method0("clear")?;
        for k in 0..new_list.len() {
            un_r2.united.bind(py).append(new_list.get_item(k)?)?;
        }
    }
    Ok(())
}

fn collect_uvars_in_union(py: Python<'_>, union: &PyObject) -> PyResult<Vec<Py<Name>>> {
    let b = union.bind(py);
    let un = b.downcast::<Union>()?.borrow();
    let lst = un.united.clone_ref(py);
    drop(un);
    let mut out = Vec::new();
    let l_b = lst.bind(py);
    for i in 0..l_b.len() {
        let item = l_b.get_item(i)?;
        if let Ok(uv) = item.downcast::<UnificationVar>() {
            out.push(uv.borrow().name.clone_ref(py));
        }
    }
    Ok(out)
}

fn collect_uvars_in_intersection(py: Python<'_>, inter: &PyObject) -> PyResult<Vec<Py<Name>>> {
    let b = inter.bind(py);
    let in_obj = b.downcast::<Intersection>()?.borrow();
    let lst = in_obj.intersected.clone_ref(py);
    drop(in_obj);
    let mut out = Vec::new();
    let l_b = lst.bind(py);
    for i in 0..l_b.len() {
        let item = l_b.get_item(i)?;
        if let Ok(uv) = item.downcast::<UnificationVar>() {
            out.push(uv.borrow().name.clone_ref(py));
        }
    }
    Ok(out)
}

fn handle_unification_in_type(
    py: Python<'_>,
    ctx: &ElaborationTypingContext,
    ty: PyObject,
) -> PyResult<PyObject> {
    let (nt, unions, intersections) = replace_unification_variables(py, ctx, ty)?;

    // 1. Removal of polar variable
    let mut all_positive: Vec<Py<Name>> = Vec::new();
    for u in &unions {
        for n in collect_uvars_in_union(py, u)? {
            all_positive.push(n);
        }
    }
    let mut all_negative: Vec<Py<Name>> = Vec::new();
    for i in &intersections {
        for n in collect_uvars_in_intersection(py, i)? {
            all_negative.push(n);
        }
    }

    let mut to_be_removed: Vec<Py<Name>> = Vec::new();
    for x in &all_positive {
        if !name_in(py, &all_negative, x) {
            to_be_removed.push(x.clone_ref(py));
        }
    }
    for x in &all_negative {
        if !name_in(py, &all_positive, x) {
            to_be_removed.push(x.clone_ref(py));
        }
    }

    // 2. Unification of indistinguishable variables (Python checks each pair
    // for all-in-all-unions / all-in-all-intersections containment, then
    // appends max(a, b) name).
    for union in &unions {
        let uvars = collect_uvars_in_union_objs(py, union)?;
        let pairs = pairs_of(&uvars);
        for (a, b) in pairs {
            let mut all_contain = true;
            for u2 in &unions {
                if !union_contains(py, u2, &a)? || !union_contains(py, u2, &b)? {
                    all_contain = false;
                    break;
                }
            }
            if all_contain {
                let a_b = a.bind(py).downcast::<UnificationVar>()?.borrow();
                let b_b = b.bind(py).downcast::<UnificationVar>()?.borrow();
                let an = a_b.name.clone_ref(py);
                let bn = b_b.name.clone_ref(py);
                drop(a_b);
                drop(b_b);
                let max = max_name(py, an, bn);
                to_be_removed.push(max);
            }
        }
    }
    for i in &intersections {
        let uvars = collect_uvars_in_intersection_objs(py, i)?;
        let pairs = pairs_of(&uvars);
        for (a, b) in pairs {
            let mut all_contain = true;
            for j in &intersections {
                if !intersection_contains(py, j, &a)? || !intersection_contains(py, j, &b)? {
                    all_contain = false;
                    break;
                }
            }
            if all_contain {
                let a_b = a.bind(py).downcast::<UnificationVar>()?.borrow();
                let b_b = b.bind(py).downcast::<UnificationVar>()?.borrow();
                let an = a_b.name.clone_ref(py);
                let bn = b_b.name.clone_ref(py);
                drop(a_b);
                drop(b_b);
                let max = max_name(py, an, bn);
                to_be_removed.push(max);
            }
        }
    }

    // 3. Flattening of variable sandwiches.
    let mut all_uvars: Vec<PyObject> = Vec::new();
    for union in &unions {
        for uv in collect_uvars_in_union_objs(py, union)? {
            all_uvars.push(uv);
        }
    }
    for u in &all_uvars {
        // pos base types: for each union containing u, all non-UV members.
        let mut pos: Vec<PyObject> = Vec::new();
        for un in &unions {
            if union_contains(py, un, u)? {
                let b = un.bind(py);
                let un_r = b.downcast::<Union>()?.borrow();
                let lst = un_r.united.clone_ref(py);
                drop(un_r);
                let l_b = lst.bind(py);
                for k in 0..l_b.len() {
                    let item = l_b.get_item(k)?;
                    if item.downcast::<UnificationVar>().is_err() {
                        pos.push(item.unbind());
                    }
                }
            }
        }
        let mut neg: Vec<PyObject> = Vec::new();
        for inter in &intersections {
            if intersection_contains(py, inter, u)? {
                let b = inter.bind(py);
                let in_r = b.downcast::<Intersection>()?.borrow();
                let lst = in_r.intersected.clone_ref(py);
                drop(in_r);
                let l_b = lst.bind(py);
                for k in 0..l_b.len() {
                    let item = l_b.get_item(k)?;
                    if item.downcast::<UnificationVar>().is_err() {
                        neg.push(item.unbind());
                    }
                }
            }
        }
        let mut overlap = false;
        for bp in &pos {
            for bn in &neg {
                if ty_equal(py, bp, bn)? {
                    overlap = true;
                    break;
                }
            }
            if overlap {
                break;
            }
        }
        if overlap {
            let uv = u.bind(py).downcast::<UnificationVar>()?.borrow();
            let n = uv.name.clone_ref(py);
            drop(uv);
            to_be_removed.push(n);
        }
    }

    remove_from_union_and_intersection(py, &unions, &intersections, &to_be_removed)?;
    remove_unions_and_intersections(py, ctx, nt)
}

fn collect_uvars_in_union_objs(py: Python<'_>, union: &PyObject) -> PyResult<Vec<PyObject>> {
    let b = union.bind(py);
    let un = b.downcast::<Union>()?.borrow();
    let lst = un.united.clone_ref(py);
    drop(un);
    let mut out = Vec::new();
    let l_b = lst.bind(py);
    for i in 0..l_b.len() {
        let item = l_b.get_item(i)?;
        if item.downcast::<UnificationVar>().is_ok() {
            out.push(item.unbind());
        }
    }
    Ok(out)
}

fn collect_uvars_in_intersection_objs(py: Python<'_>, inter: &PyObject) -> PyResult<Vec<PyObject>> {
    let b = inter.bind(py);
    let in_obj = b.downcast::<Intersection>()?.borrow();
    let lst = in_obj.intersected.clone_ref(py);
    drop(in_obj);
    let mut out = Vec::new();
    let l_b = lst.bind(py);
    for i in 0..l_b.len() {
        let item = l_b.get_item(i)?;
        if item.downcast::<UnificationVar>().is_ok() {
            out.push(item.unbind());
        }
    }
    Ok(out)
}

fn pairs_of(items: &[PyObject]) -> Vec<(PyObject, PyObject)> {
    let mut pairs = Vec::new();
    Python::with_gil(|py| {
        for i in 0..items.len() {
            for j in (i + 1)..items.len() {
                pairs.push((items[i].clone_ref(py), items[j].clone_ref(py)));
            }
        }
    });
    pairs
}

fn union_contains(py: Python<'_>, union: &PyObject, target: &PyObject) -> PyResult<bool> {
    let b = union.bind(py);
    let un = b.downcast::<Union>()?.borrow();
    let lst = un.united.clone_ref(py);
    drop(un);
    let l_b = lst.bind(py);
    for i in 0..l_b.len() {
        let item = l_b.get_item(i)?;
        if item.is(target.bind(py)) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn intersection_contains(py: Python<'_>, inter: &PyObject, target: &PyObject) -> PyResult<bool> {
    let b = inter.bind(py);
    let in_obj = b.downcast::<Intersection>()?.borrow();
    let lst = in_obj.intersected.clone_ref(py);
    drop(in_obj);
    let l_b = lst.bind(py);
    for i in 0..l_b.len() {
        let item = l_b.get_item(i)?;
        if item.is(target.bind(py)) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn max_name(py: Python<'_>, a: Py<Name>, b: Py<Name>) -> Py<Name> {
    // Python's max() on dataclass Names uses tuple ordering (name, id).
    let ab = a.borrow(py);
    let bb = b.borrow(py);
    let cmp = match ab.name.cmp(&bb.name) {
        std::cmp::Ordering::Equal => ab.id.cmp(&bb.id),
        o => o,
    };
    drop(ab);
    drop(bb);
    match cmp {
        std::cmp::Ordering::Less => b,
        _ => a,
    }
}

// =============================================================================
// elaborate_remove_unification
// =============================================================================

fn elaborate_remove_unification(
    py: Python<'_>,
    ctx: &ElaborationTypingContext,
    t: PyObject,
) -> PyResult<PyObject> {
    let b = t.bind(py);

    if b.downcast::<SLiteral>().is_ok()
        || b.downcast::<SVar>().is_ok()
        || b.downcast::<SHole>().is_ok()
        || b.downcast::<SAnonConstructor>().is_ok()
    {
        return Ok(t);
    }

    if let Ok(sa) = b.downcast::<SAnnotation>() {
        let r = sa.borrow();
        let expr = r.expr.clone_ref(py);
        let ty = r.type_.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_expr = elaborate_remove_unification(py, ctx, expr)?;
        return Ok(Py::new(
            py,
            (
                SAnnotation { expr: new_expr, type_: ty, loc },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sab) = b.downcast::<SAbstraction>() {
        let r = sab.borrow();
        let name = r.var_name.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_body = elaborate_remove_unification(py, ctx, body)?;
        return Ok(Py::new(
            py,
            (
                SAbstraction { var_name: name, body: new_body, loc },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sl) = b.downcast::<SLet>() {
        let r = sl.borrow();
        let name = r.var_name.clone_ref(py);
        let val = r.var_value.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        let mult = r.multiplicity.clone_ref(py);
        drop(r);
        let unit = st_unit(py)?;
        let nctx = ctx.with_var(py, name.clone_ref(py), unit)?;
        let new_val = elaborate_remove_unification(py, ctx, val)?;
        let new_body = elaborate_remove_unification(py, &nctx, body)?;
        return Ok(Py::new(
            py,
            (
                SLet {
                    var_name: name,
                    var_value: new_val,
                    body: new_body,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sr) = b.downcast::<SRec>() {
        let r = sr.borrow();
        let name = r.var_name.clone_ref(py);
        let ty = r.var_type.clone_ref(py);
        let val = r.var_value.clone_ref(py);
        let body = r.body.clone_ref(py);
        let decreasing_by = r.decreasing_by.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        let mult = r.multiplicity.clone_ref(py);
        drop(r);
        let nty = handle_unification_in_type(py, ctx, ty.clone_ref(py))?;
        let _nt = remove_unions_and_intersections(py, ctx, ty.clone_ref(py))?;
        let nctx = ctx.with_var(py, name.clone_ref(py), ty)?;
        let new_val = elaborate_remove_unification(py, &nctx, val)?;
        let new_body = elaborate_remove_unification(py, &nctx, body)?;
        return Ok(Py::new(
            py,
            (
                SRec {
                    var_name: name,
                    var_type: nty,
                    var_value: new_val,
                    body: new_body,
                    decreasing_by,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sif) = b.downcast::<SIf>() {
        let r = sif.borrow();
        let cond = r.cond.clone_ref(py);
        let then = r.then.clone_ref(py);
        let otherwise = r.otherwise.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_cond = elaborate_remove_unification(py, ctx, cond)?;
        let new_then = elaborate_remove_unification(py, ctx, then)?;
        let new_else = elaborate_remove_unification(py, ctx, otherwise)?;
        return Ok(Py::new(
            py,
            (
                SIf {
                    cond: new_cond,
                    then: new_then,
                    otherwise: new_else,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sap) = b.downcast::<SApplication>() {
        let r = sap.borrow();
        let fun = r.fun.clone_ref(py);
        let arg = r.arg.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_fun = elaborate_remove_unification(py, ctx, fun)?;
        let new_arg = elaborate_remove_unification(py, ctx, arg)?;
        return Ok(Py::new(
            py,
            (
                SApplication { fun: new_fun, arg: new_arg, loc },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sta) = b.downcast::<STypeAbstraction>() {
        let r = sta.borrow();
        let name = r.name.clone_ref(py);
        let kind = r.kind.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let nctx = ctx.with_typevar(py, name.clone_ref(py), kind.clone_ref(py))?;
        let new_body = elaborate_remove_unification(py, &nctx, body)?;
        return Ok(Py::new(
            py,
            (
                STypeAbstraction { name, kind, body: new_body, loc },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sra) = b.downcast::<SRefinementAbstraction>() {
        let r = sra.borrow();
        let name = r.name.clone_ref(py);
        let sort = r.sort.clone_ref(py);
        let body = r.body.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let nsort = remove_unions_and_intersections(py, ctx, sort)?;
        let new_body = elaborate_remove_unification(py, ctx, body)?;
        return Ok(Py::new(
            py,
            (
                SRefinementAbstraction {
                    name,
                    sort: nsort,
                    body: new_body,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sta) = b.downcast::<STypeApplication>() {
        let r = sta.borrow();
        let body_orig = r.body.clone_ref(py);
        let ty = r.type_.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let body = elaborate_remove_unification(py, ctx, body_orig)?;
        let nt = handle_unification_in_type(py, ctx, ty)?;

        // Case STypeConstructor("Top", _) -> return STypeApplication(body, nt, loc)
        let nt_b = nt.bind(py);
        if let Ok(stc) = nt_b.downcast::<STypeConstructor>() {
            let stc_r = stc.borrow();
            let n = stc_r.name.borrow(py);
            let is_top = n.name == "Top";
            drop(n);
            drop(stc_r);
            if is_top {
                return Ok(Py::new(
                    py,
                    (
                        STypeApplication { body, type_: nt, loc },
                        STerm,
                    ),
                )?
                .into_any());
            }
        }

        // Compute should_be_refined.
        let mut should_be_refined = true;
        if let Ok(sv) = body.bind(py).downcast::<SVar>() {
            let svr = sv.borrow();
            let name = svr.name.clone_ref(py);
            drop(svr);
            let bt = ctx.type_of(py, name)?;
            if !bt.bind(py).is_none() {
                if let Ok(stp) = bt.bind(py).downcast::<STypePolymorphism>() {
                    let stp_r = stp.borrow();
                    let kind = stp_r.kind.clone_ref(py);
                    drop(stp_r);
                    if crate::kind::is_base(py, &kind) {
                        should_be_refined = false;
                    }
                }
            }
        }

        // Match nt:
        let nt_b = nt.bind(py);
        if nt_b.downcast::<STypeConstructor>().is_ok() || nt_b.downcast::<STypeVar>().is_ok() {
            let new_type: PyObject = if should_be_refined {
                let nv = fresh_named(py, "self")?;
                let nh = fresh_named(py, "k")?;
                let hole = Py::new(
                    py,
                    (
                        SHole { name: nh, loc: default_location(py) },
                        STerm,
                    ),
                )?
                .into_any();
                Py::new(
                    py,
                    (
                        SRefinedType {
                            name: nv,
                            type_: nt,
                            refinement: hole,
                            loc: default_location(py),
                        },
                        SType,
                    ),
                )?
                .into_any()
            } else {
                nt
            };
            return Ok(Py::new(
                py,
                (
                    STypeApplication { body, type_: new_type, loc },
                    STerm,
                ),
            )?
            .into_any());
        }
        if let Ok(srt) = nt_b.downcast::<SRefinedType>() {
            let r = srt.borrow();
            let name = r.name.clone_ref(py);
            let ity = r.type_.clone_ref(py);
            drop(r);
            let nh = fresh_named(py, "k")?;
            let ref_hole = Py::new(
                py,
                (
                    SHole { name: nh, loc: default_location(py) },
                    STerm,
                ),
            )?
            .into_any();
            let new_type = Py::new(
                py,
                (
                    SRefinedType {
                        name,
                        type_: ity,
                        refinement: ref_hole,
                        loc: default_location(py),
                    },
                    SType,
                ),
            )?
            .into_any();
            return Ok(Py::new(
                py,
                (
                    STypeApplication { body, type_: new_type, loc },
                    STerm,
                ),
            )?
            .into_any());
        }
        if nt_b.downcast::<SAbstractionType>().is_ok() {
            return Ok(Py::new(
                py,
                (
                    STypeApplication { body, type_: nt, loc },
                    STerm,
                ),
            )?
            .into_any());
        }
        return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "{} ({}) not an SType.",
            nt.bind(py).str()?,
            nt.bind(py).get_type().name()?
        )));
    }

    if let Ok(sra) = b.downcast::<SRefinementApplication>() {
        let r = sra.borrow();
        let body = r.body.clone_ref(py);
        let refinement = r.refinement.clone_ref(py);
        let loc = r.loc.clone_ref(py);
        drop(r);
        let new_body = elaborate_remove_unification(py, ctx, body)?;
        let new_ref = elaborate_remove_unification(py, ctx, refinement)?;
        return Ok(Py::new(
            py,
            (
                SRefinementApplication {
                    body: new_body,
                    refinement: new_ref,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "{} ({}) not an STerm.",
        b.str()?,
        b.get_type().name()?
    )))
}

// =============================================================================
// Public Python-facing entries.
// =============================================================================

#[pyfunction]
#[pyo3(name = "elaborate_check")]
pub fn py_elaborate_check(
    py: Python<'_>,
    ctx: PyRef<'_, ElaborationTypingContext>,
    t: PyObject,
    ty: PyObject,
) -> PyResult<PyObject> {
    elaborate_check(py, &ctx, t, ty)
}

#[pyfunction]
#[pyo3(name = "elaborate_remove_unification")]
pub fn py_elaborate_remove_unification(
    py: Python<'_>,
    ctx: PyRef<'_, ElaborationTypingContext>,
    t: PyObject,
) -> PyResult<PyObject> {
    elaborate_remove_unification(py, &ctx, t)
}

#[pyfunction]
#[pyo3(signature = (ctx, e, expected_type = None))]
pub fn elaborate(
    py: Python<'_>,
    ctx: PyRef<'_, ElaborationTypingContext>,
    e: PyObject,
    expected_type: Option<PyObject>,
) -> PyResult<PyObject> {
    let expected_type = match expected_type {
        Some(t) => t,
        None => st_top(py)?,
    };
    let e2 = elaborate_foralls(py, e)?;
    let e3 = elaborate_check(py, &ctx, e2, expected_type)?;
    elaborate_remove_unification(py, &ctx, e3)
}
