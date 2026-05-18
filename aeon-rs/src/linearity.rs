//! Linearity / QTT check (port of `aeon.typechecking.linearity`).
//!
//! Walks a core term tracking per-name multiplicities and counts; emits
//! `LinearityError`s when a binder's declared multiplicity doesn't match
//! the body's actual usage. Pure-`ω` programs (the default) trigger no
//! checks.

use std::collections::HashMap;

use pyo3::prelude::*;
use pyo3::types::PyList;

use crate::liquid::LiquidVar;
use crate::name::Name;
use crate::terms::{
    Abstraction, Annotation, Application, Hole, If, Let, Literal, Rec, RefinementAbstraction,
    RefinementApplication, TypeAbstraction, TypeApplication, Var,
};
use crate::typectx::TypingContext;
use crate::types::{
    AbstractionType, ExistentialType, RefinementPolymorphism, Type, TypePolymorphism,
};

#[derive(Clone, PartialEq, Eq, Hash)]
struct NameKey {
    name: String,
    id: i64,
}

fn name_key(py: Python<'_>, n: &Py<Name>) -> NameKey {
    let n = n.borrow(py);
    NameKey { name: n.name.clone(), id: n.id }
}

enum Usage {
    /// Wraps a Python `Multiplicity` (M0/M1/MOmega/MN). We hold it as a
    /// PyObject so we can compare via `is` against the canonical singletons.
    Mult(PyObject),
    Mismatch { then_uses: i64, else_uses: i64 },
    Bottom,
}

impl Usage {
    fn cref(&self, py: Python<'_>) -> Usage {
        match self {
            Usage::Mult(m) => Usage::Mult(m.clone_ref(py)),
            Usage::Mismatch { then_uses, else_uses } => Usage::Mismatch {
                then_uses: *then_uses,
                else_uses: *else_uses,
            },
            Usage::Bottom => Usage::Bottom,
        }
    }
}

/// Clone an `(Usage, Py<Name>)` pair under the GIL.
fn clone_te(py: Python<'_>, v: &(Usage, Py<Name>)) -> (Usage, Py<Name>) {
    (v.0.cref(py), v.1.clone_ref(py))
}

struct MultRefs {
    m0: PyObject,
    m1: PyObject,
    momega: PyObject,
    mn: PyObject,
    bottom: PyObject,
    // For error construction.
    api: PyObject,
    // Operations.
    add_fn: PyObject,
    mul_fn: PyObject,
}

fn load_mult_refs(py: Python<'_>) -> PyResult<MultRefs> {
    // _BOTTOM is no longer needed (Bottom is encoded as a Usage variant);
    // we keep the field for layout compatibility.
    let bottom = py.None();
    let mult_mod = py.import_bound("aeon.core.multiplicity")?;
    Ok(MultRefs {
        m0: crate::multiplicity::m0(py),
        m1: crate::multiplicity::m1(py),
        momega: crate::multiplicity::momega(py),
        mn: crate::multiplicity::mn(py),
        bottom,
        api: py.import_bound("aeon.facade.api")?.unbind().into_any(),
        add_fn: mult_mod.getattr("add")?.unbind(),
        mul_fn: mult_mod.getattr("mul")?.unbind(),
    })
}

fn is_m(py: Python<'_>, a: &PyObject, b: &PyObject) -> bool {
    a.bind(py).is(b.bind(py))
}

fn add_mult(py: Python<'_>, refs: &MultRefs, a: &PyObject, b: &PyObject) -> PyResult<PyObject> {
    Ok(refs.add_fn.bind(py).call1((a, b))?.unbind())
}

fn mul_mult(py: Python<'_>, refs: &MultRefs, a: &PyObject, b: &PyObject) -> PyResult<PyObject> {
    Ok(refs.mul_fn.bind(py).call1((a, b))?.unbind())
}

fn add_usage(py: Python<'_>, refs: &MultRefs, a: &Usage, b: &Usage) -> PyResult<Usage> {
    match (a, b) {
        (Usage::Bottom, _) | (_, Usage::Bottom) => Ok(Usage::Bottom),
        (Usage::Mismatch { .. }, _) => Ok(a.cref(py)),
        (_, Usage::Mismatch { .. }) => Ok(b.cref(py)),
        (Usage::Mult(am), Usage::Mult(bm)) => Ok(Usage::Mult(add_mult(py, refs, am, bm)?)),
    }
}

fn scale_usage(py: Python<'_>, refs: &MultRefs, scale: &PyObject, b: &Usage) -> PyResult<Usage> {
    match b {
        Usage::Bottom => Ok(Usage::Bottom),
        Usage::Mismatch { .. } => Ok(b.cref(py)),
        Usage::Mult(bm) => Ok(Usage::Mult(mul_mult(py, refs, scale, bm)?)),
    }
}

type Tally = HashMap<NameKey, (Usage, Py<Name>)>;
type Counts = HashMap<NameKey, i64>;

fn tally_add(py: Python<'_>, refs: &MultRefs, t1: &Tally, t2: &Tally) -> PyResult<Tally> {
    let mut out: Tally = t1
        .iter()
        .map(|(k, (u, n))| (k.clone(), (u.cref(py), n.clone_ref(py))))
        .collect();
    for (n, (m, name)) in t2 {
        if let Some((existing, _)) = out.get(n).map(|v| clone_te(py, v)) {
            let new_u = add_usage(py, refs, &existing, m)?;
            out.insert(n.clone(), (new_u, name.clone_ref(py)));
        } else {
            out.insert(n.clone(), (m.cref(py), name.clone_ref(py)));
        }
    }
    Ok(out)
}

fn tally_scale(
    py: Python<'_>,
    refs: &MultRefs,
    scale: &PyObject,
    t: &Tally,
) -> PyResult<Tally> {
    if is_m(py, scale, &refs.m1) || is_m(py, scale, &refs.mn) {
        return Ok(t
            .iter()
            .map(|(k, (u, n))| (k.clone(), (u.cref(py), n.clone_ref(py))))
            .collect());
    }
    if is_m(py, scale, &refs.m0) {
        let mut out: Tally = HashMap::new();
        for (k, (u, n)) in t {
            let new_u = match u {
                Usage::Bottom => Usage::Bottom,
                _ => Usage::Mult(refs.m0.clone_ref(py)),
            };
            out.insert(k.clone(), (new_u, n.clone_ref(py)));
        }
        return Ok(out);
    }
    let mut out: Tally = HashMap::new();
    for (k, (u, n)) in t {
        out.insert(k.clone(), (scale_usage(py, refs, scale, u)?, n.clone_ref(py)));
    }
    Ok(out)
}

fn counts_add(c1: &Counts, c2: &Counts) -> Counts {
    let mut out = c1.clone();
    for (n, k) in c2 {
        *out.entry(n.clone()).or_insert(0) += k;
    }
    out
}

fn counts_scale(py: Python<'_>, refs: &MultRefs, scale: &PyObject, c: &Counts) -> Counts {
    if is_m(py, scale, &refs.m0) {
        c.keys().map(|n| (n.clone(), 0)).collect()
    } else {
        c.clone()
    }
}

fn drop_name(py: Python<'_>, tally: &Tally, counts: &Counts, key: &NameKey) -> (Tally, Counts) {
    let nt = tally
        .iter()
        .filter(|(k, _)| *k != key)
        .map(|(k, (u, n))| (k.clone(), (u.cref(py), n.clone_ref(py))))
        .collect();
    let nc = counts.iter().filter(|(k, _)| *k != key).map(|(k, v)| (k.clone(), *v)).collect();
    (nt, nc)
}

fn peel_existential(py: Python<'_>, ty: Option<PyObject>) -> Option<PyObject> {
    let mut cur = ty?;
    loop {
        let b = cur.bind(py);
        if b.is_instance_of::<ExistentialType>() {
            let body = b.downcast::<ExistentialType>().ok()?.borrow().body.clone_ref(py);
            cur = body;
            continue;
        }
        if b.is_instance_of::<TypePolymorphism>() {
            let body = b.downcast::<TypePolymorphism>().ok()?.borrow().body.clone_ref(py);
            cur = body;
            continue;
        }
        if b.is_instance_of::<RefinementPolymorphism>() {
            let body = b.downcast::<RefinementPolymorphism>().ok()?.borrow().body.clone_ref(py);
            cur = body;
            continue;
        }
        return Some(cur);
    }
}

fn term_type(py: Python<'_>, var_types: &HashMap<NameKey, (Py<Name>, PyObject)>, t: &PyObject) -> Option<PyObject> {
    let b = t.bind(py);
    if let Ok(v) = b.downcast::<Var>() {
        let nm = v.borrow().name.clone_ref(py);
        let key = name_key(py, &nm);
        return var_types.get(&key).map(|(_, t)| t.clone_ref(py));
    }
    if let Ok(an) = b.downcast::<Annotation>() {
        return Some(an.borrow().type_.clone_ref(py));
    }
    if let Ok(lit) = b.downcast::<Literal>() {
        return Some(lit.borrow().type_.clone_ref(py));
    }
    if let Ok(app) = b.downcast::<Application>() {
        let fun = app.borrow().fun.clone_ref(py);
        let ft = peel_existential(py, term_type(py, var_types, &fun));
        if let Some(t) = ft {
            if let Ok(at) = t.bind(py).downcast::<AbstractionType>() {
                return Some(at.borrow().type_.clone_ref(py));
            }
        }
        return None;
    }
    if let Ok(tap) = b.downcast::<TypeApplication>() {
        let body = tap.borrow().body.clone_ref(py);
        return peel_existential(py, term_type(py, var_types, &body));
    }
    if let Ok(rap) = b.downcast::<RefinementApplication>() {
        let body = rap.borrow().body.clone_ref(py);
        return peel_existential(py, term_type(py, var_types, &body));
    }
    None
}

fn is_native_ffi_call(py: Python<'_>, t: &PyObject) -> bool {
    fn head_is_native(py: Python<'_>, head: &PyObject) -> bool {
        if let Ok(v) = head.bind(py).downcast::<Var>() {
            let n = v.borrow().name.borrow(py).name.clone();
            return n == "native" || n == "native_import";
        }
        false
    }
    let mut head = t.clone_ref(py);
    loop {
        let b = head.bind(py);
        if let Ok(an) = b.downcast::<Annotation>() {
            head = an.borrow().expr.clone_ref(py);
            continue;
        }
        if let Ok(tap) = b.downcast::<TypeApplication>() {
            head = tap.borrow().body.clone_ref(py);
            continue;
        }
        if let Ok(rap) = b.downcast::<RefinementApplication>() {
            head = rap.borrow().body.clone_ref(py);
            continue;
        }
        break;
    }
    if head_is_native(py, &head) {
        return true;
    }
    if let Ok(app) = head.bind(py).downcast::<Application>() {
        let mut cur = head.clone_ref(py);
        while let Ok(a) = cur.bind(py).downcast::<Application>() {
            cur = a.borrow().fun.clone_ref(py);
        }
        // Strip type / refinement applications.
        loop {
            let b = cur.bind(py);
            if let Ok(tap) = b.downcast::<TypeApplication>() {
                cur = tap.borrow().body.clone_ref(py);
                continue;
            }
            if let Ok(rap) = b.downcast::<RefinementApplication>() {
                cur = rap.borrow().body.clone_ref(py);
                continue;
            }
            break;
        }
        let _ = app;
        return head_is_native(py, &cur);
    }
    false
}

struct Walker {
    var_types: HashMap<NameKey, (Py<Name>, PyObject)>,
    in_scope: HashMap<NameKey, Py<Name>>,
}

impl Walker {
    fn with_var(&self, py: Python<'_>, name: &Py<Name>, ty: Option<&PyObject>) -> Self {
        let key = name_key(py, name);
        let mut new_types: HashMap<NameKey, (Py<Name>, PyObject)> = self
            .var_types
            .iter()
            .map(|(k, (n, t))| (k.clone(), (n.clone_ref(py), t.clone_ref(py))))
            .collect();
        if let Some(t) = ty {
            new_types.insert(key.clone(), (name.clone_ref(py), t.clone_ref(py)));
        } else {
            new_types.remove(&key);
        }
        let mut new_scope: HashMap<NameKey, Py<Name>> = self
            .in_scope
            .iter()
            .map(|(k, n)| (k.clone(), n.clone_ref(py)))
            .collect();
        new_scope.insert(key, name.clone_ref(py));
        Walker {
            var_types: new_types,
            in_scope: new_scope,
        }
    }

    fn native_bottom_tally(&self, py: Python<'_>) -> (Tally, Counts) {
        let mut out: Tally = HashMap::new();
        for (k, n) in &self.in_scope {
            out.insert(k.clone(), (Usage::Bottom, n.clone_ref(py)));
        }
        (out, HashMap::new())
    }

    fn tally(
        &self,
        py: Python<'_>,
        refs: &MultRefs,
        term: &PyObject,
    ) -> PyResult<(Tally, Counts)> {
        if is_native_ffi_call(py, term) {
            return Ok(self.native_bottom_tally(py));
        }
        let b = term.bind(py);
        if let Ok(v) = b.downcast::<Var>() {
            let n = v.borrow().name.clone_ref(py);
            let key = name_key(py, &n);
            let mut t = Tally::new();
            t.insert(key.clone(), (Usage::Mult(refs.m1.clone_ref(py)), n));
            let mut c = Counts::new();
            c.insert(key, 1);
            return Ok((t, c));
        }
        if b.is_instance_of::<Literal>() || b.is_instance_of::<Hole>() {
            return Ok((HashMap::new(), HashMap::new()));
        }
        if let Ok(an) = b.downcast::<Annotation>() {
            let expr = an.borrow().expr.clone_ref(py);
            return self.tally(py, refs, &expr);
        }
        if let Ok(app) = b.downcast::<Application>() {
            let app = app.borrow();
            let fun = app.fun.clone_ref(py);
            let arg = app.arg.clone_ref(py);
            drop(app);
            let (ft, fc) = self.tally(py, refs, &fun)?;
            let (at, ac) = self.tally(py, refs, &arg)?;
            let fun_ty = peel_existential(py, term_type(py, &self.var_types, &fun));
            let pmult = match fun_ty {
                Some(ft) => {
                    if let Ok(at) = ft.bind(py).downcast::<AbstractionType>() {
                        at.borrow().multiplicity.clone_ref(py)
                    } else {
                        refs.m1.clone_ref(py)
                    }
                }
                None => refs.m1.clone_ref(py),
            };
            let scaled_t = tally_scale(py, refs, &pmult, &at)?;
            let scaled_c = counts_scale(py, refs, &pmult, &ac);
            return Ok((
                tally_add(py, refs, &ft, &scaled_t)?,
                counts_add(&fc, &scaled_c),
            ));
        }
        if let Ok(ab) = b.downcast::<Abstraction>() {
            let ab = ab.borrow();
            let n = ab.var_name.clone_ref(py);
            let body = ab.body.clone_ref(py);
            drop(ab);
            let inner = self.with_var(py, &n, None);
            let (bt, bc) = inner.tally(py, refs, &body)?;
            let key = name_key(py, &n);
            let (nt, nc) = drop_name(py, &bt, &bc, &key);
            return Ok((nt, nc));
        }
        if let Ok(le) = b.downcast::<Let>() {
            let le = le.borrow();
            let n = le.var_name.clone_ref(py);
            let val = le.var_value.clone_ref(py);
            let body = le.body.clone_ref(py);
            drop(le);
            let val_ty = term_type(py, &self.var_types, &val);
            let inner = self.with_var(py, &n, val_ty.as_ref());
            let (bt, bc) = inner.tally(py, refs, &body)?;
            // Alias projection: let n = x — fold n into x in body.
            if let Ok(v) = val.bind(py).downcast::<Var>() {
                let target = v.borrow().name.clone_ref(py);
                if !names_equal(py, &target, &n) {
                    let (bt2, bc2) = alias_project(py, &bt, &bc, &n, &target, refs)?;
                    return Ok((bt2, bc2));
                }
            }
            let (vt, vc) = self.tally(py, refs, &val)?;
            let key = name_key(py, &n);
            let (bt2, bc2) = drop_name(py, &bt, &bc, &key);
            return Ok((tally_add(py, refs, &vt, &bt2)?, counts_add(&vc, &bc2)));
        }
        if let Ok(rc) = b.downcast::<Rec>() {
            let rc = rc.borrow();
            let n = rc.var_name.clone_ref(py);
            let var_type = rc.var_type.clone_ref(py);
            let val = rc.var_value.clone_ref(py);
            let body = rc.body.clone_ref(py);
            drop(rc);
            let inner = self.with_var(py, &n, Some(&var_type));
            let (vt, vc) = inner.tally(py, refs, &val)?;
            let (bt, bc) = inner.tally(py, refs, &body)?;
            let key = name_key(py, &n);
            let (vt, vc) = drop_name(py, &vt, &vc, &key);
            let (bt, bc) = drop_name(py, &bt, &bc, &key);
            return Ok((tally_add(py, refs, &vt, &bt)?, counts_add(&vc, &bc)));
        }
        if let Ok(ife) = b.downcast::<If>() {
            let ife = ife.borrow();
            let cond = ife.cond.clone_ref(py);
            let then = ife.then.clone_ref(py);
            let otherwise = ife.otherwise.clone_ref(py);
            drop(ife);
            let (ct, cc) = self.tally(py, refs, &cond)?;
            let (tt, tc) = self.tally(py, refs, &then)?;
            let (et, ec) = self.tally(py, refs, &otherwise)?;
            let (merged_t, merged_c) = branch_merge(py, refs, &tt, &tc, &et, &ec)?;
            return Ok((
                tally_add(py, refs, &ct, &merged_t)?,
                counts_add(&cc, &merged_c),
            ));
        }
        if let Ok(tap) = b.downcast::<TypeApplication>() {
            let body = tap.borrow().body.clone_ref(py);
            return self.tally(py, refs, &body);
        }
        if let Ok(rap) = b.downcast::<RefinementApplication>() {
            let body = rap.borrow().body.clone_ref(py);
            return self.tally(py, refs, &body);
        }
        if let Ok(ta) = b.downcast::<TypeAbstraction>() {
            let body = ta.borrow().body.clone_ref(py);
            return self.tally(py, refs, &body);
        }
        if let Ok(rab) = b.downcast::<RefinementAbstraction>() {
            let body = rab.borrow().body.clone_ref(py);
            return self.tally(py, refs, &body);
        }
        Ok((HashMap::new(), HashMap::new()))
    }
}

fn names_equal(py: Python<'_>, a: &Py<Name>, b: &Py<Name>) -> bool {
    let a = a.borrow(py);
    let b = b.borrow(py);
    a.name == b.name && a.id == b.id
}

fn alias_project(
    py: Python<'_>,
    tally: &Tally,
    counts: &Counts,
    name: &Py<Name>,
    target: &Py<Name>,
    refs: &MultRefs,
) -> PyResult<(Tally, Counts)> {
    let name_key_v = name_key(py, name);
    if names_equal(py, name, target) {
        return Ok(drop_name(py, tally, counts, &name_key_v));
    }
    let target_key = name_key(py, target);
    let n_use = tally.get(&name_key_v).map(|(u, _)| u.cref(py));
    let n_count = counts.get(&name_key_v).copied().unwrap_or(0);
    let mut nt: Tally = tally
        .iter()
        .filter(|(k, _)| **k != name_key_v)
        .map(|(k, (u, n))| (k.clone(), (u.cref(py), n.clone_ref(py))))
        .collect();
    let mut nc: Counts = counts
        .iter()
        .filter(|(k, _)| **k != name_key_v)
        .map(|(k, v)| (k.clone(), *v))
        .collect();
    let is_m0 = match &n_use {
        Some(Usage::Mult(m)) => is_m(py, m, &refs.m0),
        _ => false,
    };
    if let Some(u) = n_use {
        if !is_m0 {
            let existing = nt
                .get(&target_key)
                .map(|v| v.0.cref(py))
                .unwrap_or(Usage::Mult(refs.m0.clone_ref(py)));
            let new_u = add_usage(py, refs, &existing, &u)?;
            nt.insert(target_key.clone(), (new_u, target.clone_ref(py)));
            *nc.entry(target_key).or_insert(0) += n_count;
        }
    }
    Ok((nt, nc))
}

fn branch_merge(
    py: Python<'_>,
    refs: &MultRefs,
    tt: &Tally,
    tc: &Counts,
    et: &Tally,
    ec: &Counts,
) -> PyResult<(Tally, Counts)> {
    let mut keys: Vec<NameKey> = tt.keys().chain(et.keys()).cloned().collect();
    keys.sort_by(|a, b| a.name.cmp(&b.name).then(a.id.cmp(&b.id)));
    keys.dedup();
    let mut out_t: Tally = HashMap::new();
    for k in keys {
        let v_then = tt.get(&k).map(|v| clone_te(py, v));
        let v_else = et.get(&k).map(|v| clone_te(py, v));
        let v_then_u = v_then.as_ref().map(|(u, _)| u.cref(py)).unwrap_or(Usage::Mult(refs.m0.clone_ref(py)));
        let v_else_u = v_else.as_ref().map(|(u, _)| u.cref(py)).unwrap_or(Usage::Mult(refs.m0.clone_ref(py)));
        let canonical_name = v_then
            .as_ref()
            .or(v_else.as_ref())
            .map(|(_, n)| n.clone_ref(py))
            .unwrap();
        if matches!(v_then_u, Usage::Bottom) || matches!(v_else_u, Usage::Bottom) {
            out_t.insert(k, (Usage::Bottom, canonical_name));
            continue;
        }
        if matches!(v_then_u, Usage::Mismatch { .. }) {
            out_t.insert(k, (v_then_u, canonical_name));
            continue;
        }
        if matches!(v_else_u, Usage::Mismatch { .. }) {
            out_t.insert(k, (v_else_u, canonical_name));
            continue;
        }
        let equal = match (&v_then_u, &v_else_u) {
            (Usage::Mult(a), Usage::Mult(b)) => is_m(py, a, b),
            _ => false,
        };
        if equal {
            out_t.insert(k, (v_then_u, canonical_name));
        } else {
            let then_uses = tc.get(&k).copied().unwrap_or(0);
            let else_uses = ec.get(&k).copied().unwrap_or(0);
            out_t.insert(k, (Usage::Mismatch { then_uses, else_uses }, canonical_name));
        }
    }
    let mut out_c: Counts = HashMap::new();
    for k in tc.keys().chain(ec.keys()) {
        let v = tc.get(k).copied().unwrap_or(0).max(ec.get(k).copied().unwrap_or(0));
        out_c.insert(k.clone(), v);
    }
    Ok((out_t, out_c))
}

fn binder_body(py: Python<'_>, term: &PyObject) -> Option<PyObject> {
    let b = term.bind(py);
    if let Ok(le) = b.downcast::<Let>() {
        return Some(le.borrow().body.clone_ref(py));
    }
    if let Ok(ab) = b.downcast::<Abstraction>() {
        return Some(ab.borrow().body.clone_ref(py));
    }
    if let Ok(rc) = b.downcast::<Rec>() {
        return Some(rc.borrow().body.clone_ref(py));
    }
    None
}

fn find_var_uses(py: Python<'_>, term: &PyObject, name: &Py<Name>) -> PyResult<Vec<PyObject>> {
    let mut out: Vec<PyObject> = Vec::new();
    walk_var_uses(py, term, name, &mut out)?;
    Ok(out)
}

fn walk_var_uses(
    py: Python<'_>,
    t: &PyObject,
    name: &Py<Name>,
    out: &mut Vec<PyObject>,
) -> PyResult<()> {
    let b = t.bind(py);
    if let Ok(v) = b.downcast::<Var>() {
        let v = v.borrow();
        if names_equal(py, &v.name, name) {
            out.push(v.loc.clone_ref(py));
        }
        return Ok(());
    }
    if b.is_instance_of::<Literal>() || b.is_instance_of::<Hole>() {
        return Ok(());
    }
    if let Ok(an) = b.downcast::<Annotation>() {
        let e = an.borrow().expr.clone_ref(py);
        return walk_var_uses(py, &e, name, out);
    }
    if let Ok(app) = b.downcast::<Application>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        drop(app);
        walk_var_uses(py, &fun, name, out)?;
        return walk_var_uses(py, &arg, name, out);
    }
    if let Ok(ab) = b.downcast::<Abstraction>() {
        let ab = ab.borrow();
        let n = ab.var_name.clone_ref(py);
        let body = ab.body.clone_ref(py);
        drop(ab);
        if names_equal(py, &n, name) {
            return Ok(());
        }
        return walk_var_uses(py, &body, name, out);
    }
    if let Ok(le) = b.downcast::<Let>() {
        let le = le.borrow();
        let n = le.var_name.clone_ref(py);
        let val = le.var_value.clone_ref(py);
        let body = le.body.clone_ref(py);
        drop(le);
        walk_var_uses(py, &val, name, out)?;
        if names_equal(py, &n, name) {
            return Ok(());
        }
        return walk_var_uses(py, &body, name, out);
    }
    if let Ok(rc) = b.downcast::<Rec>() {
        let rc = rc.borrow();
        let n = rc.var_name.clone_ref(py);
        let val = rc.var_value.clone_ref(py);
        let body = rc.body.clone_ref(py);
        drop(rc);
        if names_equal(py, &n, name) {
            return Ok(());
        }
        walk_var_uses(py, &val, name, out)?;
        return walk_var_uses(py, &body, name, out);
    }
    if let Ok(ife) = b.downcast::<If>() {
        let ife = ife.borrow();
        let cond = ife.cond.clone_ref(py);
        let then = ife.then.clone_ref(py);
        let otherwise = ife.otherwise.clone_ref(py);
        drop(ife);
        walk_var_uses(py, &cond, name, out)?;
        walk_var_uses(py, &then, name, out)?;
        return walk_var_uses(py, &otherwise, name, out);
    }
    if let Ok(tap) = b.downcast::<TypeApplication>() {
        let body = tap.borrow().body.clone_ref(py);
        return walk_var_uses(py, &body, name, out);
    }
    if let Ok(rap) = b.downcast::<RefinementApplication>() {
        let body = rap.borrow().body.clone_ref(py);
        return walk_var_uses(py, &body, name, out);
    }
    if let Ok(ta) = b.downcast::<TypeAbstraction>() {
        let body = ta.borrow().body.clone_ref(py);
        return walk_var_uses(py, &body, name, out);
    }
    if let Ok(rab) = b.downcast::<RefinementAbstraction>() {
        let body = rab.borrow().body.clone_ref(py);
        return walk_var_uses(py, &body, name, out);
    }
    Ok(())
}

fn raise_error(py: Python<'_>, refs: &MultRefs, cls: &str, args: &Bound<'_, pyo3::types::PyTuple>) -> PyResult<PyObject> {
    let api = refs.api.bind(py);
    let cls = api.getattr(cls)?;
    Ok(cls.call1(args)?.unbind())
}

fn check_binder(
    py: Python<'_>,
    refs: &MultRefs,
    name: &Py<Name>,
    multiplicity: &PyObject,
    body_tally: &Tally,
    body_counts: &Counts,
    term: &PyObject,
    errors: &Bound<'_, PyList>,
    declared_kw: bool,
) -> PyResult<()> {
    if is_m(py, multiplicity, &refs.momega) || is_m(py, multiplicity, &refs.mn) {
        return Ok(());
    }
    let key = name_key(py, name);
    let use_val = body_tally.get(&key).map(|(u, _)| u.cref(py)).unwrap_or(Usage::Mult(refs.m0.clone_ref(py)));
    let count = body_counts.get(&key).copied().unwrap_or(0);

    if matches!(use_val, Usage::Bottom) {
        return Ok(());
    }
    let body_opt = binder_body(py, term);
    let use_locs = match &body_opt {
        Some(b) => find_var_uses(py, b, name)?,
        None => Vec::new(),
    };
    let use_locs_list = PyList::new_bound(py, use_locs.iter()).unbind();

    let is_m0 = is_m(py, multiplicity, &refs.m0);

    if let Usage::Mismatch { then_uses, else_uses } = use_val {
        let _ = use_locs_list;
        if is_m0 {
            let api = refs.api.bind(py);
            let cls = api.getattr("ErasedUsedAtRuntimeError")?;
            let kwargs = pyo3::types::PyDict::new_bound(py);
            kwargs.set_item("name", name.clone_ref(py))?;
            kwargs.set_item("term", term.clone_ref(py))?;
            let locs_clone: Vec<PyObject> = use_locs.iter().map(|o| o.clone_ref(py)).collect();
            kwargs.set_item("use_locations", locs_clone)?;
            let err = cls.call((), Some(&kwargs))?;
            errors.append(err)?;
        } else {
            let api = refs.api.bind(py);
            let cls = api.getattr("LinearBranchMismatchError")?;
            let kwargs = pyo3::types::PyDict::new_bound(py);
            kwargs.set_item("name", name.clone_ref(py))?;
            kwargs.set_item("then_uses", then_uses)?;
            kwargs.set_item("else_uses", else_uses)?;
            kwargs.set_item("term", term.clone_ref(py))?;
            let err = cls.call((), Some(&kwargs))?;
            errors.append(err)?;
        }
        let _ = declared_kw;
        return Ok(());
    }

    if is_m0 {
        let is_u_m0 = match &use_val {
            Usage::Mult(m) => is_m(py, m, &refs.m0),
            _ => false,
        };
        if !is_u_m0 {
            let api = refs.api.bind(py);
            let cls = api.getattr("ErasedUsedAtRuntimeError")?;
            let kwargs = pyo3::types::PyDict::new_bound(py);
            kwargs.set_item("name", name.clone_ref(py))?;
            kwargs.set_item("term", term.clone_ref(py))?;
            let locs_clone: Vec<PyObject> = use_locs.iter().map(|o| o.clone_ref(py)).collect();
            kwargs.set_item("use_locations", locs_clone)?;
            let err = cls.call((), Some(&kwargs))?;
            errors.append(err)?;
        }
        return Ok(());
    }

    // multiplicity is M1
    let is_u_m0 = match &use_val {
        Usage::Mult(m) => is_m(py, m, &refs.m0),
        _ => false,
    };
    let is_u_momega = match &use_val {
        Usage::Mult(m) => is_m(py, m, &refs.momega),
        _ => false,
    };
    if is_u_m0 {
        let api = refs.api.bind(py);
        let cls = api.getattr("LinearUnusedError")?;
        let kwargs = pyo3::types::PyDict::new_bound(py);
        kwargs.set_item("name", name.clone_ref(py))?;
        kwargs.set_item("declared", multiplicity.clone_ref(py))?;
        kwargs.set_item("term", term.clone_ref(py))?;
        let err = cls.call((), Some(&kwargs))?;
        errors.append(err)?;
        return Ok(());
    }
    if is_u_momega {
        let (cause, actual) = if count >= 2 {
            ("syntactic", count)
        } else {
            ("scaled-to-omega", count.max(1))
        };
        let api = refs.api.bind(py);
        let cls = api.getattr("LinearUsedTooManyTimesError")?;
        let kwargs = pyo3::types::PyDict::new_bound(py);
        kwargs.set_item("name", name.clone_ref(py))?;
        kwargs.set_item("declared", multiplicity.clone_ref(py))?;
        kwargs.set_item("actual_uses", actual)?;
        kwargs.set_item("term", term.clone_ref(py))?;
        let locs_clone: Vec<PyObject> = use_locs.iter().map(|o| o.clone_ref(py)).collect();
        kwargs.set_item("use_locations", locs_clone)?;
        kwargs.set_item("cause", cause)?;
        let err = cls.call((), Some(&kwargs))?;
        errors.append(err)?;
        return Ok(());
    }
    // use is M1 — exactly the linear obligation. OK.
    Ok(())
}

fn visit_term(
    py: Python<'_>,
    refs: &MultRefs,
    node: &PyObject,
    walker: &Walker,
    expected_ty: Option<&PyObject>,
    errors: &Bound<'_, PyList>,
) -> PyResult<()> {
    let b = node.bind(py);
    if b.is_instance_of::<Literal>() || b.is_instance_of::<Var>() || b.is_instance_of::<Hole>() {
        return Ok(());
    }
    if let Ok(an) = b.downcast::<Annotation>() {
        let expr = an.borrow().expr.clone_ref(py);
        return visit_term(py, refs, &expr, walker, expected_ty, errors);
    }
    if let Ok(app) = b.downcast::<Application>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        drop(app);
        visit_term(py, refs, &fun, walker, None, errors)?;
        let fun_ty = peel_existential(py, term_type(py, &walker.var_types, &fun));
        let inner_ty = match &fun_ty {
            Some(t) => {
                if let Ok(at) = t.bind(py).downcast::<AbstractionType>() {
                    Some(at.borrow().var_type.clone_ref(py))
                } else {
                    None
                }
            }
            None => None,
        };
        return visit_term(py, refs, &arg, walker, inner_ty.as_ref(), errors);
    }
    if let Ok(ab) = b.downcast::<Abstraction>() {
        let ab = ab.borrow();
        let name = ab.var_name.clone_ref(py);
        let body = ab.body.clone_ref(py);
        drop(ab);
        let ety = peel_existential(py, expected_ty.map(|e| e.clone_ref(py)));
        let (param_mult, inner_ty, body_ty): (PyObject, Option<PyObject>, Option<PyObject>) = match ety {
            Some(t) => {
                if let Ok(at) = t.bind(py).downcast::<AbstractionType>() {
                    let at = at.borrow();
                    (
                        at.multiplicity.clone_ref(py),
                        Some(at.var_type.clone_ref(py)),
                        Some(at.type_.clone_ref(py)),
                    )
                } else {
                    (refs.momega.clone_ref(py), None, None)
                }
            }
            None => (refs.momega.clone_ref(py), None, None),
        };
        let inner = walker.with_var(py, &name, inner_ty.as_ref());
        let (bt, bc) = inner.tally(py, refs, &body)?;
        check_binder(py, refs, &name, &param_mult, &bt, &bc, node, errors, false)?;
        return visit_term(py, refs, &body, &inner, body_ty.as_ref(), errors);
    }
    if let Ok(le) = b.downcast::<Let>() {
        let le = le.borrow();
        let name = le.var_name.clone_ref(py);
        let val = le.var_value.clone_ref(py);
        let body = le.body.clone_ref(py);
        let mult = le.multiplicity.clone_ref(py);
        drop(le);
        let val_ty = term_type(py, &walker.var_types, &val);
        let inner = walker.with_var(py, &name, val_ty.as_ref());
        let (bt, bc) = inner.tally(py, refs, &body)?;
        check_binder(py, refs, &name, &mult, &bt, &bc, node, errors, false)?;
        visit_term(py, refs, &val, walker, None, errors)?;
        return visit_term(py, refs, &body, &inner, None, errors);
    }
    if let Ok(rc) = b.downcast::<Rec>() {
        let rc = rc.borrow();
        let name = rc.var_name.clone_ref(py);
        let var_type = rc.var_type.clone_ref(py);
        let val = rc.var_value.clone_ref(py);
        let body = rc.body.clone_ref(py);
        let mult = rc.multiplicity.clone_ref(py);
        drop(rc);
        let inner = walker.with_var(py, &name, Some(&var_type));
        let (bt, bc) = inner.tally(py, refs, &body)?;
        check_binder(py, refs, &name, &mult, &bt, &bc, node, errors, false)?;
        visit_term(py, refs, &val, &inner, Some(&var_type), errors)?;
        return visit_term(py, refs, &body, &inner, None, errors);
    }
    if let Ok(ife) = b.downcast::<If>() {
        let ife = ife.borrow();
        let cond = ife.cond.clone_ref(py);
        let then = ife.then.clone_ref(py);
        let otherwise = ife.otherwise.clone_ref(py);
        drop(ife);
        visit_term(py, refs, &cond, walker, None, errors)?;
        visit_term(py, refs, &then, walker, expected_ty, errors)?;
        return visit_term(py, refs, &otherwise, walker, expected_ty, errors);
    }
    if let Ok(tap) = b.downcast::<TypeApplication>() {
        let body = tap.borrow().body.clone_ref(py);
        return visit_term(py, refs, &body, walker, expected_ty, errors);
    }
    if let Ok(rap) = b.downcast::<RefinementApplication>() {
        let body = rap.borrow().body.clone_ref(py);
        return visit_term(py, refs, &body, walker, expected_ty, errors);
    }
    if let Ok(ta) = b.downcast::<TypeAbstraction>() {
        let body = ta.borrow().body.clone_ref(py);
        return visit_term(py, refs, &body, walker, expected_ty, errors);
    }
    if let Ok(rab) = b.downcast::<RefinementAbstraction>() {
        let body = rab.borrow().body.clone_ref(py);
        return visit_term(py, refs, &body, walker, expected_ty, errors);
    }
    Ok(())
}

#[pyfunction]
#[pyo3(signature = (term, ctx = None))]
pub fn check_linearity(
    py: Python<'_>,
    term: PyObject,
    ctx: Option<&Bound<'_, TypingContext>>,
) -> PyResult<Py<PyList>> {
    let refs = load_mult_refs(py)?;
    let errors = PyList::empty_bound(py);

    let mut initial_types: HashMap<NameKey, (Py<Name>, PyObject)> = HashMap::new();
    let mut in_scope: HashMap<NameKey, Py<Name>> = HashMap::new();
    if let Some(c) = ctx {
        let vars = c.borrow().vars(py)?;
        let vars_b = vars.bind(py);
        for i in 0..vars_b.len() {
            let tup = vars_b.get_item(i)?;
            let nm: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let ty: PyObject = tup.get_item(1)?.unbind();
            let key = name_key(py, &nm);
            initial_types.insert(key.clone(), (nm.clone_ref(py), ty));
            in_scope.insert(key, nm);
        }
    }
    let walker = Walker { var_types: initial_types, in_scope };
    visit_term(py, &refs, &term, &walker, None, &errors)?;
    Ok(errors.unbind())
}

#[allow(dead_code)]
fn _silence(_t: &Type, _lv: &LiquidVar) {}
