//! Verification-condition constraints + alpha-equivalence canonicalization.
//! Mirrors aeon.verification.vcs.
//!
//! The `alpha_key` cache key sits on the hot path of every smt_valid call
//! (cache lookup), and the `_alpha_*` walks are pure recursion over the
//! AST — ideal port target.

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::liquid::{
    LiquidApp, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt, LiquidLiteralString,
    LiquidVar,
};
use crate::loc::resolve_loc;
use crate::name::Name;
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, TypeConstructor, TypePolymorphism,
    TypeVar,
};

// =========================================================================
// Constraint hierarchy — mirrors the dataclasses in vcs.py
// =========================================================================

#[pyclass(module = "aeon_rs", subclass)]
pub struct Constraint;

#[pymethods]
impl Constraint {
    #[new]
    #[pyo3(signature = (*_args, **_kwargs))]
    fn py_new(
        _args: &Bound<'_, PyTuple>,
        _kwargs: Option<&Bound<'_, pyo3::types::PyDict>>,
    ) -> Self {
        Constraint
    }
}

fn hash_via_str(obj: &Bound<'_, PyAny>) -> PyResult<u64> {
    use std::collections::hash_map::DefaultHasher;
    let mut h = DefaultHasher::new();
    obj.str()?.to_string().hash(&mut h);
    Ok(h.finish())
}

// ---- LiquidConstraint ----
#[pyclass(module = "aeon_rs", extends = Constraint)]
pub struct LiquidConstraint {
    #[pyo3(get, set)]
    pub expr: PyObject,
    #[pyo3(get, set)]
    pub loc: Option<PyObject>,
}

#[pymethods]
impl LiquidConstraint {
    #[new]
    #[pyo3(signature = (expr, loc = None))]
    fn py_new(expr: PyObject, loc: Option<PyObject>) -> (Self, Constraint) {
        (LiquidConstraint { expr, loc }, Constraint)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["expr", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(self.expr.bind(py).repr()?.to_string())
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<LiquidConstraint>() {
            Ok(o) => self.expr.bind(py).eq(o.borrow().expr.bind(py)),
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- Conjunction ----
#[pyclass(module = "aeon_rs", extends = Constraint)]
pub struct Conjunction {
    #[pyo3(get, set)]
    pub c1: PyObject,
    #[pyo3(get, set)]
    pub c2: PyObject,
    #[pyo3(get, set)]
    pub loc: Option<PyObject>,
}

#[pymethods]
impl Conjunction {
    #[new]
    #[pyo3(signature = (c1, c2, loc = None))]
    fn py_new(c1: PyObject, c2: PyObject, loc: Option<PyObject>) -> (Self, Constraint) {
        (Conjunction { c1, c2, loc }, Constraint)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["c1", "c2", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "({}) ∧ ({})",
            self.c1.bind(py).str()?,
            self.c2.bind(py).str()?
        ))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<Conjunction>() {
            Ok(o) => {
                let o = o.borrow();
                Ok(self.c1.bind(py).eq(o.c1.bind(py))? && self.c2.bind(py).eq(o.c2.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- UninterpretedFunctionDeclaration ----
#[pyclass(module = "aeon_rs", extends = Constraint)]
pub struct UninterpretedFunctionDeclaration {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set, name = "type")]
    pub type_: PyObject,
    #[pyo3(get, set)]
    pub seq: PyObject,
}

#[pymethods]
impl UninterpretedFunctionDeclaration {
    #[new]
    fn py_new(name: Py<Name>, r#type: PyObject, seq: PyObject) -> (Self, Constraint) {
        (
            UninterpretedFunctionDeclaration { name, type_: r#type, seq },
            Constraint,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "type", "seq"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "fun {}:{} => {}",
            self.name.borrow(py).__str__(),
            self.type_.bind(py).str()?,
            self.seq.bind(py).str()?,
        ))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<UninterpretedFunctionDeclaration>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                Ok(a.name == b.name
                    && a.id == b.id
                    && self.type_.bind(py).eq(o.type_.bind(py))?
                    && self.seq.bind(py).eq(o.seq.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- ReflectedFunctionDeclaration ----
#[pyclass(module = "aeon_rs", extends = Constraint)]
pub struct ReflectedFunctionDeclaration {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set, name = "type")]
    pub type_: PyObject,
    #[pyo3(get, set)]
    pub params: Py<PyTuple>,
    #[pyo3(get, set)]
    pub body: PyObject,
    #[pyo3(get, set)]
    pub seq: PyObject,
}

#[pymethods]
impl ReflectedFunctionDeclaration {
    #[new]
    fn py_new(
        name: Py<Name>,
        r#type: PyObject,
        params: Py<PyTuple>,
        body: PyObject,
        seq: PyObject,
    ) -> (Self, Constraint) {
        (
            ReflectedFunctionDeclaration { name, type_: r#type, params, body, seq },
            Constraint,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "type", "params", "body", "seq"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let l = self.params.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            parts.push(l.get_item(i)?.str()?.to_string());
        }
        Ok(format!(
            "reflected {}({}):{} = {} => {}",
            self.name.borrow(py).__str__(),
            parts.join(", "),
            self.type_.bind(py).str()?,
            self.body.bind(py).str()?,
            self.seq.bind(py).str()?,
        ))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<ReflectedFunctionDeclaration>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                Ok(a.name == b.name
                    && a.id == b.id
                    && self.type_.bind(py).eq(o.type_.bind(py))?
                    && self.params.bind(py).eq(o.params.bind(py))?
                    && self.body.bind(py).eq(o.body.bind(py))?
                    && self.seq.bind(py).eq(o.seq.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- Implication ----
#[pyclass(module = "aeon_rs", extends = Constraint)]
pub struct Implication {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set)]
    pub base: PyObject,
    #[pyo3(get, set)]
    pub pred: PyObject,
    #[pyo3(get, set)]
    pub seq: PyObject,
    #[pyo3(get, set)]
    pub loc: Option<PyObject>,
}

#[pymethods]
impl Implication {
    #[new]
    #[pyo3(signature = (name, base, pred, seq, loc = None))]
    fn py_new(
        name: Py<Name>,
        base: PyObject,
        pred: PyObject,
        seq: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Constraint) {
        // __post_init__: assert isinstance(name, Name) — guaranteed by Py<Name> type.
        (Implication { name, base, pred, seq, loc }, Constraint)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "base", "pred", "seq", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "∀{}:{}, ({}) => {}",
            self.name.borrow(py).__str__(),
            self.base.bind(py).str()?,
            self.pred.bind(py).str()?,
            self.seq.bind(py).str()?,
        ))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<Implication>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                Ok(a.name == b.name
                    && a.id == b.id
                    && self.base.bind(py).eq(o.base.bind(py))?
                    && self.pred.bind(py).eq(o.pred.bind(py))?
                    && self.seq.bind(py).eq(o.seq.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- TypeVarDeclaration ----
#[pyclass(module = "aeon_rs", extends = Constraint)]
pub struct TypeVarDeclaration {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set)]
    pub seq: PyObject,
}

#[pymethods]
impl TypeVarDeclaration {
    #[new]
    fn py_new(name: Py<Name>, seq: PyObject) -> (Self, Constraint) {
        (TypeVarDeclaration { name, seq }, Constraint)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "seq"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "type {}, {}",
            self.name.borrow(py).__str__(),
            self.seq.bind(py).str()?,
        ))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<TypeVarDeclaration>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                Ok(a.name == b.name
                    && a.id == b.id
                    && self.seq.bind(py).eq(o.seq.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// =========================================================================
// alpha_key — alpha-equivalent canonical string for cache lookup
// =========================================================================

type Env = HashMap<(String, i64), usize>;

fn alpha_name_of(env: &Env, name_str: &str, name_id: i64) -> String {
    if let Some(c) = env.get(&(name_str.to_string(), name_id)) {
        format!("{}#{}", name_str, c)
    } else {
        // not a bound variable — keep the original str() form
        if name_id == 0 {
            name_str.to_string()
        } else if name_id == -1 {
            format!("{}?", name_str)
        } else {
            format!("{}{}", name_str, super_sup(name_id))
        }
    }
}

fn super_sup(n: i64) -> String {
    let digits = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];
    let mut out = String::new();
    let mut s = n.to_string();
    if s.starts_with('-') {
        out.push('⁻');
        s = s[1..].to_string();
    }
    for ch in s.chars() {
        match ch.to_digit(10) {
            Some(d) => out.push(digits[d as usize]),
            None => out.push(ch),
        }
    }
    out
}

fn alpha_bind(env: &Env, counter: &mut usize, name: &Name) -> (String, Env) {
    let key = (name.name.clone(), name.id);
    let canonical = *counter;
    *counter += 1;
    let mut new_env = env.clone();
    new_env.insert(key, canonical);
    (format!("{}#{}", name.name, canonical), new_env)
}

fn alpha_liquid(py: Python<'_>, t: &Bound<'_, PyAny>, env: &Env, counter: &mut usize) -> PyResult<String> {
    if let Ok(b) = t.downcast::<LiquidLiteralBool>() {
        return Ok(if b.borrow().value { "true".to_string() } else { "false".to_string() });
    }
    if let Ok(i) = t.downcast::<LiquidLiteralInt>() {
        return Ok(i.borrow().value.to_string());
    }
    if let Ok(f) = t.downcast::<LiquidLiteralFloat>() {
        return Ok(f.borrow().value.to_string());
    }
    if let Ok(s) = t.downcast::<LiquidLiteralString>() {
        return Ok(format!("{:?}", s.borrow().value));
    }
    if let Ok(v) = t.downcast::<LiquidVar>() {
        let v = v.borrow();
        let n = v.name.borrow(py);
        return Ok(alpha_name_of(env, &n.name, n.id));
    }
    if let Ok(app) = t.downcast::<LiquidApp>() {
        let app = app.borrow();
        let fun_n = app.fun.borrow(py);
        let fun_s = alpha_name_of(env, &fun_n.name, fun_n.id);
        let args = app.args.bind(py);
        let is_op = !fun_n.name.is_empty() && fun_n.name.chars().all(|c| !c.is_alphanumeric());
        if is_op && args.len() == 2 {
            let a1 = alpha_liquid(py, &args.get_item(0)?, env, counter)?;
            let a2 = alpha_liquid(py, &args.get_item(1)?, env, counter)?;
            return Ok(format!("({} {} {})", a1, fun_s, a2));
        }
        let mut parts: Vec<String> = Vec::with_capacity(args.len());
        for i in 0..args.len() {
            parts.push(alpha_liquid(py, &args.get_item(i)?, env, counter)?);
        }
        return Ok(format!("{}({})", fun_s, parts.join(",")));
    }
    // Fallback for LiquidHornApplication etc. — repr()
    Ok(t.repr()?.to_string())
}

fn alpha_type(py: Python<'_>, ty: &Bound<'_, PyAny>, env: &Env, counter: &mut usize) -> PyResult<String> {
    if let Ok(at) = ty.downcast::<AbstractionType>() {
        let at = at.borrow();
        let n = at.var_name.borrow(py);
        let (var_s, new_env) = alpha_bind(env, counter, &n);
        drop(n);
        let vt_s = alpha_type(py, at.var_type.bind(py), &new_env, counter)?;
        let body_s = alpha_type(py, at.type_.bind(py), &new_env, counter)?;
        return Ok(format!("({}:{}) -> {}", var_s, vt_s, body_s));
    }
    if let Ok(rt) = ty.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let n = rt.name.borrow(py);
        let (var_s, new_env) = alpha_bind(env, counter, &n);
        drop(n);
        let base_s = alpha_type(py, rt.type_.bind(py), &new_env, counter)?;
        let ref_s = alpha_liquid(py, rt.refinement.bind(py), &new_env, counter)?;
        return Ok(format!("{{{}:{} | {}}}", var_s, base_s, ref_s));
    }
    if let Ok(tc) = ty.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let n = tc.name.borrow(py);
        let args = tc.args.bind(py);
        let name_str = name_to_str(&n);
        if args.len() > 0 {
            let mut parts: Vec<String> = Vec::with_capacity(args.len());
            for i in 0..args.len() {
                parts.push(alpha_type(py, &args.get_item(i)?, env, counter)?);
            }
            return Ok(format!("{} {}", name_str, parts.join(" ")));
        }
        return Ok(name_str);
    }
    if let Ok(tv) = ty.downcast::<TypeVar>() {
        let tv = tv.borrow();
        let n = tv.name.borrow(py);
        return Ok(alpha_name_of(env, &n.name, n.id));
    }
    if ty.is_instance_of::<Top>() {
        return Ok("⊤".to_string());
    }
    if let Ok(tp) = ty.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let n = tp.name.borrow(py);
        let (var_s, new_env) = alpha_bind(env, counter, &n);
        drop(n);
        let body_s = alpha_type(py, tp.body.bind(py), &new_env, counter)?;
        let kind_s = tp.kind.bind(py).str()?.to_string();
        return Ok(format!("forall {}:{}, {}", var_s, kind_s, body_s));
    }
    if let Ok(rp) = ty.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let n = rp.name.borrow(py);
        let (var_s, new_env) = alpha_bind(env, counter, &n);
        drop(n);
        let sort_s = alpha_type(py, rp.sort.bind(py), &new_env, counter)?;
        let body_s = alpha_type(py, rp.body.bind(py), &new_env, counter)?;
        return Ok(format!("forall <{}:{} -> Bool>, {}", var_s, sort_s, body_s));
    }
    Ok(ty.repr()?.to_string())
}

fn name_to_str(n: &Name) -> String {
    if n.id == 0 {
        n.name.clone()
    } else if n.id == -1 {
        format!("{}?", n.name)
    } else {
        format!("{}{}", n.name, super_sup(n.id))
    }
}

fn alpha_constraint(py: Python<'_>, c: &Bound<'_, PyAny>, env: &Env, counter: &mut usize) -> PyResult<String> {
    if let Ok(lc) = c.downcast::<LiquidConstraint>() {
        let lc = lc.borrow();
        return alpha_liquid(py, lc.expr.bind(py), env, counter);
    }
    if let Ok(conj) = c.downcast::<Conjunction>() {
        let conj = conj.borrow();
        let left = alpha_constraint(py, conj.c1.bind(py), env, counter)?;
        let right = alpha_constraint(py, conj.c2.bind(py), env, counter)?;
        return Ok(format!("({}) ∧ ({})", left, right));
    }
    if let Ok(imp) = c.downcast::<Implication>() {
        let imp = imp.borrow();
        let n = imp.name.borrow(py);
        let (var_s, new_env) = alpha_bind(env, counter, &n);
        drop(n);
        let base_s = alpha_type(py, imp.base.bind(py), &new_env, counter)?;
        let pred_s = alpha_liquid(py, imp.pred.bind(py), &new_env, counter)?;
        let seq_s = alpha_constraint(py, imp.seq.bind(py), &new_env, counter)?;
        return Ok(format!("∀{}:{}, ({}) => {}", var_s, base_s, pred_s, seq_s));
    }
    if let Ok(ufd) = c.downcast::<UninterpretedFunctionDeclaration>() {
        let ufd = ufd.borrow();
        let n = ufd.name.borrow(py);
        let (var_s, new_env) = alpha_bind(env, counter, &n);
        drop(n);
        let type_s = alpha_type(py, ufd.type_.bind(py), &new_env, counter)?;
        let seq_s = alpha_constraint(py, ufd.seq.bind(py), &new_env, counter)?;
        return Ok(format!("fun {}:{} => {}", var_s, type_s, seq_s));
    }
    if let Ok(rfd) = c.downcast::<ReflectedFunctionDeclaration>() {
        let rfd = rfd.borrow();
        let n = rfd.name.borrow(py);
        let (var_s, mut new_env) = alpha_bind(env, counter, &n);
        drop(n);
        let params = rfd.params.bind(py);
        let mut params_strs: Vec<String> = Vec::with_capacity(params.len());
        for i in 0..params.len() {
            let p: Py<Name> = params.get_item(i)?.extract()?;
            let pn = p.borrow(py);
            let (p_s, ne) = alpha_bind(&new_env, counter, &pn);
            drop(pn);
            params_strs.push(p_s);
            new_env = ne;
        }
        let type_s = alpha_type(py, rfd.type_.bind(py), &new_env, counter)?;
        let body_s = alpha_liquid(py, rfd.body.bind(py), &new_env, counter)?;
        let seq_s = alpha_constraint(py, rfd.seq.bind(py), &new_env, counter)?;
        return Ok(format!(
            "reflected {}({}):{} = {} => {}",
            var_s,
            params_strs.join(", "),
            type_s,
            body_s,
            seq_s
        ));
    }
    if let Ok(tvd) = c.downcast::<TypeVarDeclaration>() {
        let tvd = tvd.borrow();
        let n = tvd.name.borrow(py);
        let (var_s, new_env) = alpha_bind(env, counter, &n);
        drop(n);
        let seq_s = alpha_constraint(py, tvd.seq.bind(py), &new_env, counter)?;
        return Ok(format!("type {}, {}", var_s, seq_s));
    }
    Ok(c.repr()?.to_string())
}

/// Compute an alpha-equivalent canonical string for a constraint.
#[pyfunction]
pub fn alpha_key(py: Python<'_>, c: PyObject) -> PyResult<String> {
    let env: Env = HashMap::new();
    let mut counter = 0usize;
    alpha_constraint(py, c.bind(py), &env, &mut counter)
}

// =========================================================================
// variables_in_liq / variables_free_in
// =========================================================================

fn collect_vars_in_liq(py: Python<'_>, t: &Bound<'_, PyAny>, out: &Bound<'_, PyList>) -> PyResult<()> {
    if t.is_instance_of::<LiquidLiteralBool>()
        || t.is_instance_of::<LiquidLiteralInt>()
        || t.is_instance_of::<LiquidLiteralString>()
    {
        return Ok(());
    }
    if let Ok(v) = t.downcast::<LiquidVar>() {
        let v = v.borrow();
        let n = v.name.borrow(py);
        out.append(name_to_str(&n))?;
        return Ok(());
    }
    if let Ok(app) = t.downcast::<LiquidApp>() {
        let app = app.borrow();
        let fn_n = app.fun.borrow(py);
        out.append(name_to_str(&fn_n))?;
        drop(fn_n);
        let args = app.args.bind(py);
        for i in 0..args.len() {
            collect_vars_in_liq(py, &args.get_item(i)?, out)?;
        }
    }
    Ok(())
}

#[pyfunction]
pub fn variables_in_liq(py: Python<'_>, t: PyObject) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    collect_vars_in_liq(py, t.bind(py), &out)?;
    Ok(out.unbind())
}

fn collect_vars_free_in(py: Python<'_>, c: &Bound<'_, PyAny>, out: &Bound<'_, PyList>) -> PyResult<()> {
    if let Ok(conj) = c.downcast::<Conjunction>() {
        let conj = conj.borrow();
        collect_vars_free_in(py, conj.c1.bind(py), out)?;
        collect_vars_free_in(py, conj.c2.bind(py), out)?;
        return Ok(());
    }
    if let Ok(imp) = c.downcast::<Implication>() {
        let imp = imp.borrow();
        let bound_name = {
            let n = imp.name.borrow(py);
            name_to_str(&n)
        };
        // pred vars: filter out the bound name
        let tmp = PyList::empty_bound(py);
        collect_vars_in_liq(py, imp.pred.bind(py), &tmp)?;
        for i in 0..tmp.len() {
            let k = tmp.get_item(i)?.extract::<String>()?;
            if k != bound_name {
                out.append(k)?;
            }
        }
        // seq vars: filter out the bound name
        let tmp2 = PyList::empty_bound(py);
        collect_vars_free_in(py, imp.seq.bind(py), &tmp2)?;
        for i in 0..tmp2.len() {
            let k = tmp2.get_item(i)?.extract::<String>()?;
            if k != bound_name {
                out.append(k)?;
            }
        }
        return Ok(());
    }
    if let Ok(lc) = c.downcast::<LiquidConstraint>() {
        let lc = lc.borrow();
        return collect_vars_in_liq(py, lc.expr.bind(py), out);
    }
    if let Ok(rfd) = c.downcast::<ReflectedFunctionDeclaration>() {
        let rfd = rfd.borrow();
        collect_vars_in_liq(py, rfd.body.bind(py), out)?;
        collect_vars_free_in(py, rfd.seq.bind(py), out)?;
        return Ok(());
    }
    Ok(())
}

#[pyfunction]
pub fn variables_free_in(py: Python<'_>, c: PyObject) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    collect_vars_free_in(py, c.bind(py), &out)?;
    Ok(out.unbind())
}
