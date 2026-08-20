//! LiquidTerm hierarchy. Mirrors aeon.core.liquid plus LiquidHornApplication
//! which originally lives in aeon.core.types to avoid a circular import.

use pyo3::prelude::*;
use pyo3::types::PyTuple;
use std::hash::{Hash, Hasher};

use crate::loc::resolve_loc;
use crate::name::Name;

// ---------- Base class ----------

#[pyclass(module = "aeon_rs", subclass)]
pub struct LiquidTerm;

#[pymethods]
impl LiquidTerm {
    // Accept (and ignore) arbitrary args so Python subclasses
    // (LiquidHornApplication in aeon.core.types, etc.) can pass their own
    // dataclass arguments through super().__new__.
    #[new]
    #[pyo3(signature = (*_args, **_kwargs))]
    fn py_new(_args: &Bound<'_, PyTuple>, _kwargs: Option<&Bound<'_, pyo3::types::PyDict>>) -> Self {
        LiquidTerm
    }
}

// ---------- LiquidHole ----------

#[pyclass(module = "aeon_rs", extends = LiquidTerm, frozen)]
pub struct LiquidHole;

#[pymethods]
impl LiquidHole {
    #[new]
    fn py_new() -> (Self, LiquidTerm) {
        (LiquidHole, LiquidTerm)
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other.is_instance_of::<LiquidHole>()
    }

    fn __hash__(&self) -> u64 {
        0xC0FFEE_AAAA
    }

    fn __repr__(&self) -> &'static str {
        "?"
    }
}

// ---------- Literal helpers (macro to cut down boilerplate) ----------

macro_rules! liquid_literal {
    ($cls:ident, $field:ty, $hash_seed:expr) => {
        #[pyclass(module = "aeon_rs", extends = LiquidTerm, frozen)]
        pub struct $cls {
            #[pyo3(get)]
            pub value: $field,
            #[pyo3(get)]
            pub loc: PyObject,
        }

        #[pymethods]
        impl $cls {
            #[new]
            #[pyo3(signature = (value, loc = None))]
            fn py_new(py: Python<'_>, value: $field, loc: Option<PyObject>) -> (Self, LiquidTerm) {
                ($cls { value, loc: resolve_loc(py, loc) }, LiquidTerm)
            }

            #[classattr]
            fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
                PyTuple::new_bound(py, &["value", "loc"])
            }

            fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
                match other.downcast::<$cls>() {
                    Ok(o) => o.borrow().value == self.value,
                    Err(_) => false,
                }
            }

            fn __hash__(&self) -> u64 {
                use std::collections::hash_map::DefaultHasher;
                let mut h = DefaultHasher::new();
                $hash_seed.hash(&mut h);
                hash_payload(&self.value, &mut h);
                h.finish()
            }

            fn __repr__(&self) -> String {
                format!("{:?}", self.value).to_lowercase()
            }
        }
    };
}

trait HashPayload {
    fn hash_into<H: Hasher>(&self, h: &mut H);
}
impl HashPayload for bool {
    fn hash_into<H: Hasher>(&self, h: &mut H) { self.hash(h) }
}
impl HashPayload for i64 {
    fn hash_into<H: Hasher>(&self, h: &mut H) { self.hash(h) }
}
impl HashPayload for f64 {
    fn hash_into<H: Hasher>(&self, h: &mut H) { self.to_bits().hash(h) }
}
impl HashPayload for String {
    fn hash_into<H: Hasher>(&self, h: &mut H) { self.hash(h) }
}

fn hash_payload<T: HashPayload, H: Hasher>(v: &T, h: &mut H) {
    v.hash_into(h)
}

liquid_literal!(LiquidLiteralBool, bool, 0u8);
liquid_literal!(LiquidLiteralInt, i64, 1u8);
liquid_literal!(LiquidLiteralFloat, f64, 2u8);
liquid_literal!(LiquidLiteralString, String, 3u8);

// ---------- LiquidLiteralUnit (the lone Unit-typed liquid value) ----------
// Distinct from LiquidLiteralBool(True): Unit has its own SMT sort with
// exactly one element, so `unit == True` is ill-typed and rejected at the
// liquid layer rather than silently true at the SMT layer.

#[pyclass(module = "aeon_rs", extends = LiquidTerm, frozen)]
pub struct LiquidLiteralUnit {
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl LiquidLiteralUnit {
    #[new]
    #[pyo3(signature = (loc = None))]
    fn py_new(py: Python<'_>, loc: Option<PyObject>) -> (Self, LiquidTerm) {
        (LiquidLiteralUnit { loc: resolve_loc(py, loc) }, LiquidTerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["loc"])
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other.downcast::<LiquidLiteralUnit>().is_ok()
    }

    fn __hash__(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        let mut h = DefaultHasher::new();
        "()".hash(&mut h);
        h.finish()
    }

    fn __repr__(&self) -> &'static str {
        "()"
    }
}

// ---------- LiquidVar ----------

#[pyclass(module = "aeon_rs", extends = LiquidTerm, frozen)]
pub struct LiquidVar {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl LiquidVar {
    #[new]
    #[pyo3(signature = (name, loc = None))]
    fn py_new(py: Python<'_>, name: Py<Name>, loc: Option<PyObject>) -> (Self, LiquidTerm) {
        (LiquidVar { name, loc: resolve_loc(py, loc) }, LiquidTerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "loc"])
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<LiquidVar>() {
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
        let mut h = DefaultHasher::new();
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        h.finish()
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        self.name.borrow(py).__str__()
    }
}

// ---------- LiquidApp ----------

#[pyclass(module = "aeon_rs", extends = LiquidTerm, frozen)]
pub struct LiquidApp {
    #[pyo3(get)]
    pub fun: Py<Name>,
    #[pyo3(get)]
    pub args: Py<pyo3::types::PyList>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl LiquidApp {
    #[new]
    #[pyo3(signature = (fun, args, loc = None))]
    fn py_new(
        py: Python<'_>,
        fun: Py<Name>,
        args: Py<pyo3::types::PyList>,
        loc: Option<PyObject>,
    ) -> (Self, LiquidTerm) {
        (LiquidApp { fun, args, loc: resolve_loc(py, loc) }, LiquidTerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["fun", "args", "loc"])
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<LiquidApp>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.fun.borrow(py);
                let b = o.fun.borrow(py);
                if !(a.name == b.name && a.id == b.id) {
                    return Ok(false);
                }
                let la = self.args.bind(py);
                let lb = o.args.bind(py);
                if la.len() != lb.len() {
                    return Ok(false);
                }
                for i in 0..la.len() {
                    let x = la.get_item(i)?;
                    let y = lb.get_item(i)?;
                    if !x.eq(&y)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        let mut h = DefaultHasher::new();
        let n = self.fun.borrow(py);
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        let l = self.args.bind(py);
        for i in 0..l.len() {
            let x = l.get_item(i)?;
            let xh: isize = x.hash()?;
            xh.hash(&mut h);
        }
        Ok(h.finish())
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let fn_name = self.fun.borrow(py);
        let l = self.args.bind(py);
        let is_op = !fn_name.name.is_empty()
            && fn_name.name.chars().all(|c| !c.is_alphanumeric());
        if is_op && l.len() == 2 {
            let a1 = l.get_item(0)?.repr()?.to_string();
            let a2 = l.get_item(1)?.repr()?.to_string();
            return Ok(format!("({} {} {})", a1, fn_name.__str__(), a2));
        }
        let mut parts: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            parts.push(l.get_item(i)?.repr()?.to_string());
        }
        Ok(format!("{}({})", fn_name.__str__(), parts.join(",")))
    }
}

// ---------- LiquidHornApplication ----------
// argtypes: list[tuple[LiquidTerm, TypeConstructor | TypeVar]]
// Defined here (not types.rs) so we can keep Type hierarchy ignorant of liquid

#[pyclass(module = "aeon_rs", extends = LiquidTerm, frozen)]
pub struct LiquidHornApplication {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub argtypes: Py<pyo3::types::PyList>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl LiquidHornApplication {
    #[new]
    #[pyo3(signature = (name, argtypes, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        argtypes: Py<pyo3::types::PyList>,
        loc: Option<PyObject>,
    ) -> (Self, LiquidTerm) {
        (
            LiquidHornApplication { name, argtypes, loc: resolve_loc(py, loc) },
            LiquidTerm,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "argtypes", "loc"])
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<LiquidHornApplication>() {
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
        use std::collections::hash_map::DefaultHasher;
        let mut h = DefaultHasher::new();
        let n = self.name.borrow(py);
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        h.finish()
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let name = self.name.borrow(py);
        let l = self.argtypes.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            let tup = l.get_item(i)?;
            let n: String = tup.get_item(0)?.repr()?.to_string();
            let t: String = tup.get_item(1)?.repr()?.to_string();
            parts.push(format!("{}:{}", n, t));
        }
        Ok(format!("?{}({})", name.__str__(), parts.join(", ")))
    }
}


// =============================================================================
// liquid_free_vars — collect all Names referenced in a LiquidTerm. Mirrors
// `aeon.core.liquid.liquid_free_vars`. Variables under LiquidVar are
// included; function names under LiquidApp are also included (matches the
// Python contract). LiquidHornApplication and literals contribute nothing.
// =============================================================================

#[pyfunction]
pub fn liquid_free_vars(py: Python<'_>, e: PyObject) -> PyResult<Py<pyo3::types::PyList>> {
    let out = pyo3::types::PyList::empty_bound(py);
    lfv_into(py, e, &out)?;
    Ok(out.unbind())
}

fn lfv_into(
    py: Python<'_>,
    e: PyObject,
    out: &pyo3::Bound<'_, pyo3::types::PyList>,
) -> PyResult<()> {
    let bound = e.bind(py);
    if let Ok(v) = bound.downcast::<LiquidVar>() {
        out.append(v.borrow().name.clone_ref(py))?;
        return Ok(());
    }
    if let Ok(app) = bound.downcast::<LiquidApp>() {
        let app = app.borrow();
        out.append(app.fun.clone_ref(py))?;
        let args = app.args.bind(py);
        for i in 0..args.len() {
            let a = args.get_item(i)?.unbind();
            lfv_into(py, a, out)?;
        }
        return Ok(());
    }
    // Literals + LiquidHole + LiquidHornApplication contribute no free vars.
    Ok(())
}

/// `ensure_liqterm(a)` — wrap a `Name` in a `LiquidVar` (no-op for a
/// LiquidTerm). Mirrors `aeon.core.liquid.ensure_liqterm`.
#[pyfunction]
pub fn ensure_liqterm(py: Python<'_>, a: PyObject) -> PyResult<PyObject> {
    let b = a.bind(py);
    if let Ok(n) = b.downcast::<crate::name::Name>() {
        let name: Py<crate::name::Name> = n.clone().unbind();
        let lv = Py::new(
            py,
            (
                LiquidVar { name, loc: crate::loc::default_location(py) },
                LiquidTerm,
            ),
        )?;
        return Ok(lv.into_any());
    }
    Ok(a)
}

/// `is_safe_for_application(x)` — true iff `x` is a value-like
/// LiquidTerm (a variable or a literal). Mirrors the Python original.
#[pyfunction]
pub fn is_safe_for_application(py: Python<'_>, x: PyObject) -> bool {
    let b = x.bind(py);
    b.downcast::<LiquidVar>().is_ok()
        || b.downcast::<LiquidLiteralBool>().is_ok()
        || b.downcast::<LiquidLiteralFloat>().is_ok()
        || b.downcast::<LiquidLiteralInt>().is_ok()
        || b.downcast::<LiquidLiteralString>().is_ok()
        || b.downcast::<LiquidLiteralUnit>().is_ok()
}
