//! Surface (sugar) AST: SType, STerm, and the Node hierarchy.
//! Mirrors aeon.sugar.stypes and aeon.sugar.program.
//!
//! Container-shaped fields (lists / dicts / tuples of mixed AST nodes) are
//! kept as opaque `PyObject` — the parser builds them as Python collections
//! and downstream passes consume them; there's nothing Rust-specific to gain
//! by unpacking them here.

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};
use std::hash::{Hash, Hasher};

use crate::loc::resolve_loc;
use crate::name::Name;

fn hash_str(s: &str) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    let mut h = DefaultHasher::new();
    s.hash(&mut h);
    h.finish()
}

fn hash_via_str(obj: &Bound<'_, PyAny>) -> PyResult<u64> {
    Ok(hash_str(&obj.str()?.to_string()))
}

// =========================================================================
// SType hierarchy
// =========================================================================

#[pyclass(module = "aeon_rs", subclass)]
pub struct SType;

#[pymethods]
impl SType {
    // Accept (and ignore) arbitrary args so Python subclasses
    // (UnificationVar, Union, Intersection in aeon.elaboration) can pass
    // their own constructor arguments through super().__new__.
    #[new]
    #[pyo3(signature = (*_args, **_kwargs))]
    fn py_new(_args: &Bound<'_, PyTuple>, _kwargs: Option<&Bound<'_, pyo3::types::PyDict>>) -> Self {
        SType
    }
}

#[pyclass(module = "aeon_rs", extends = SType, frozen)]
pub struct STypeVar {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl STypeVar {
    #[new]
    #[pyo3(signature = (name, loc = None))]
    fn py_new(py: Python<'_>, name: Py<Name>, loc: Option<PyObject>) -> (Self, SType) {
        (STypeVar { name, loc: resolve_loc(py, loc) }, SType)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> String {
        format!("'{}", self.name.borrow(py).__str__())
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<STypeVar>() {
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
}

#[pyclass(module = "aeon_rs", extends = SType, frozen)]
pub struct SRefinedType {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
    #[pyo3(get)]
    pub refinement: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SRefinedType {
    #[new]
    #[pyo3(signature = (name, r#type, refinement, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        r#type: PyObject,
        refinement: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, SType) {
        (SRefinedType { name, type_: r#type, refinement, loc: resolve_loc(py, loc) }, SType)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "type", "refinement", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "{{{} : {} | {} }}",
            self.name.borrow(py).__str__(),
            self.type_.bind(py).str()?,
            self.refinement.bind(py).str()?
        ))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SRefinedType>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                Ok(a.name == b.name
                    && a.id == b.id
                    && self.type_.bind(py).eq(o.type_.bind(py))?
                    && self.refinement.bind(py).eq(o.refinement.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        Ok(hash_str(&self.__str__(py)?))
    }
}

#[pyclass(module = "aeon_rs", extends = SType, frozen)]
pub struct SAbstractionType {
    #[pyo3(get)]
    pub var_name: Py<Name>,
    #[pyo3(get)]
    pub var_type: PyObject,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SAbstractionType {
    #[new]
    #[pyo3(signature = (var_name, var_type, r#type, loc = None))]
    fn py_new(
        py: Python<'_>,
        var_name: Py<Name>,
        var_type: PyObject,
        r#type: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, SType) {
        (
            SAbstractionType { var_name, var_type, type_: r#type, loc: resolve_loc(py, loc) },
            SType,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["var_name", "var_type", "type", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "({} : {}) -> {}",
            self.var_name.borrow(py).__str__(),
            self.var_type.bind(py).str()?,
            self.type_.bind(py).str()?
        ))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SAbstractionType>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.var_name.borrow(py);
                let b = o.var_name.borrow(py);
                Ok(a.name == b.name
                    && a.id == b.id
                    && self.var_type.bind(py).eq(o.var_type.bind(py))?
                    && self.type_.bind(py).eq(o.type_.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        Ok(hash_str(&self.__str__(py)?))
    }
}

#[pyclass(module = "aeon_rs", extends = SType, frozen)]
pub struct STypePolymorphism {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub kind: PyObject,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl STypePolymorphism {
    #[new]
    #[pyo3(signature = (name, kind, body, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        kind: PyObject,
        body: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, SType) {
        (STypePolymorphism { name, kind, body, loc: resolve_loc(py, loc) }, SType)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "kind", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "∀{}:{}. {}",
            self.name.borrow(py).__str__(),
            self.kind.bind(py).str()?,
            self.body.bind(py).str()?
        ))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<STypePolymorphism>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                Ok(a.name == b.name
                    && a.id == b.id
                    && self.kind.bind(py).eq(o.kind.bind(py))?
                    && self.body.bind(py).eq(o.body.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        Ok(hash_str(&self.__str__(py)?))
    }
}

#[pyclass(module = "aeon_rs", extends = SType, frozen)]
pub struct SRefinementPolymorphism {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub sort: PyObject,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SRefinementPolymorphism {
    #[new]
    #[pyo3(signature = (name, sort, body, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        sort: PyObject,
        body: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, SType) {
        (SRefinementPolymorphism { name, sort, body, loc: resolve_loc(py, loc) }, SType)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "sort", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "∀<{}:{} -> Bool>. {}",
            self.name.borrow(py).__str__(),
            self.sort.bind(py).str()?,
            self.body.bind(py).str()?
        ))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SRefinementPolymorphism>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                Ok(a.name == b.name
                    && a.id == b.id
                    && self.sort.bind(py).eq(o.sort.bind(py))?
                    && self.body.bind(py).eq(o.body.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        Ok(hash_str(&self.__str__(py)?))
    }
}

#[pyclass(module = "aeon_rs", extends = SType, frozen)]
pub struct STypeConstructor {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub args: Py<PyList>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl STypeConstructor {
    #[new]
    #[pyo3(signature = (name, args = None, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        args: Option<Py<PyList>>,
        loc: Option<PyObject>,
    ) -> (Self, SType) {
        let args = args.unwrap_or_else(|| PyList::empty_bound(py).unbind());
        (STypeConstructor { name, args, loc: resolve_loc(py, loc) }, SType)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "args", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let l = self.args.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            parts.push(l.get_item(i)?.str()?.to_string());
        }
        Ok(format!("{} {}", self.name.borrow(py).__str__(), parts.join(", ")))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<STypeConstructor>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                if !(a.name == b.name && a.id == b.id) {
                    return Ok(false);
                }
                let la = self.args.bind(py);
                let lb = o.args.bind(py);
                if la.len() != lb.len() {
                    return Ok(false);
                }
                for i in 0..la.len() {
                    if !la.get_item(i)?.eq(&lb.get_item(i)?)? {
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
        let n = self.name.borrow(py);
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        let l = self.args.bind(py);
        for i in 0..l.len() {
            let xh: isize = l.get_item(i)?.hash()?;
            xh.hash(&mut h);
        }
        Ok(h.finish())
    }
}

// =========================================================================
// STerm hierarchy
// =========================================================================

#[pyclass(module = "aeon_rs", subclass)]
pub struct STerm;

#[pymethods]
impl STerm {
    #[new]
    fn py_new() -> Self {
        STerm
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SLiteral ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SLiteral {
    #[pyo3(get)]
    pub value: PyObject,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SLiteral {
    #[new]
    #[pyo3(signature = (value, r#type, loc = None))]
    fn py_new(py: Python<'_>, value: PyObject, r#type: PyObject, loc: Option<PyObject>) -> (Self, STerm) {
        (SLiteral { value, type_: r#type, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["value", "type", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let v = self.value.bind(py);
        if v.is_instance_of::<pyo3::types::PyString>() {
            Ok(format!("\"{}\"", v.str()?))
        } else {
            Ok(v.str()?.to_string().to_lowercase())
        }
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        // Python: if type == STypeConstructor(Name("String",0)): quoted
        let ty = self.type_.bind(py);
        let is_string = if let Ok(tc) = ty.downcast::<STypeConstructor>() {
            let tc = tc.borrow();
            let n = tc.name.borrow(py);
            n.id == 0 && n.name == "String" && tc.args.bind(py).len() == 0
        } else {
            false
        };
        if is_string {
            Ok(format!("\"{}\"", self.value.bind(py).str()?))
        } else {
            Ok(self.value.bind(py).str()?.to_string())
        }
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SLiteral>() {
            Ok(o) => {
                let o = o.borrow();
                Ok(self.value.bind(py).eq(o.value.bind(py))?
                    && self.type_.bind(py).eq(o.type_.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SVar ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SVar {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SVar {
    #[new]
    #[pyo3(signature = (name, loc = None))]
    fn py_new(py: Python<'_>, name: Py<Name>, loc: Option<PyObject>) -> (Self, STerm) {
        (SVar { name, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> String {
        self.name.borrow(py).__str__()
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!("Var({})", self.name.borrow(py).__str__())
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<SVar>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                a.name == b.name && a.id == b.id
            }
            Err(_) => false,
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SQualifiedVar ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SQualifiedVar {
    #[pyo3(get)]
    pub qualifier: String,
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SQualifiedVar {
    #[new]
    #[pyo3(signature = (qualifier, name, loc = None))]
    fn py_new(py: Python<'_>, qualifier: String, name: Py<Name>, loc: Option<PyObject>) -> (Self, STerm) {
        (SQualifiedVar { qualifier, name, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["qualifier", "name", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> String {
        format!("{}.{}", self.qualifier, self.name.borrow(py).__str__())
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!("QVar({}.{})", self.qualifier, self.name.borrow(py).__str__())
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SAnnotation ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SAnnotation {
    #[pyo3(get)]
    pub expr: PyObject,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SAnnotation {
    #[new]
    #[pyo3(signature = (expr, r#type, loc = None))]
    fn py_new(py: Python<'_>, expr: PyObject, r#type: PyObject, loc: Option<PyObject>) -> (Self, STerm) {
        (SAnnotation { expr, type_: r#type, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["expr", "type", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!("({} : {})", self.expr.bind(py).str()?, self.type_.bind(py).str()?))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SAnnotation>() {
            Ok(o) => Ok(self.expr.bind(py).eq(o.borrow().expr.bind(py))?),
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SHole ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SHole {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SHole {
    #[new]
    #[pyo3(signature = (name, loc = None))]
    fn py_new(py: Python<'_>, name: Py<Name>, loc: Option<PyObject>) -> (Self, STerm) {
        (SHole { name, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> String {
        format!("?{}", self.name.borrow(py).__str__())
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!("Hole({})", self.name.borrow(py).__str__())
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<SHole>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                a.name == b.name && a.id == b.id
            }
            Err(_) => false,
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SBy ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SBy {
    #[pyo3(get)]
    pub steps: Py<PyTuple>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SBy {
    #[new]
    #[pyo3(signature = (steps, loc = None))]
    fn py_new(py: Python<'_>, steps: Py<PyTuple>, loc: Option<PyObject>) -> (Self, STerm) {
        (SBy { steps, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["steps", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let l = self.steps.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            parts.push(l.get_item(i)?.str()?.to_string());
        }
        Ok(format!("by {}", parts.join("; ")))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!("SBy({})", self.steps.bind(py).repr()?))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SBy>() {
            Ok(o) => Ok(self.steps.bind(py).eq(o.borrow().steps.bind(py))?),
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SApplication ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SApplication {
    #[pyo3(get)]
    pub fun: PyObject,
    #[pyo3(get)]
    pub arg: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SApplication {
    #[new]
    #[pyo3(signature = (fun, arg, loc = None))]
    fn py_new(py: Python<'_>, fun: PyObject, arg: PyObject, loc: Option<PyObject>) -> (Self, STerm) {
        (SApplication { fun, arg, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["fun", "arg", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!("({} {})", self.fun.bind(py).str()?, self.arg.bind(py).str()?))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SApplication>() {
            Ok(o) => {
                let o = o.borrow();
                Ok(self.fun.bind(py).eq(o.fun.bind(py))? && self.arg.bind(py).eq(o.arg.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SAbstraction ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SAbstraction {
    #[pyo3(get)]
    pub var_name: Py<Name>,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SAbstraction {
    #[new]
    #[pyo3(signature = (var_name, body, loc = None))]
    fn py_new(py: Python<'_>, var_name: Py<Name>, body: PyObject, loc: Option<PyObject>) -> (Self, STerm) {
        (SAbstraction { var_name, body, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["var_name", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!("(\\{} -> {})", self.var_name.borrow(py).__str__(), self.body.bind(py).str()?))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SAbstraction>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.var_name.borrow(py);
                let b = o.var_name.borrow(py);
                Ok(a.name == b.name && a.id == b.id && self.body.bind(py).eq(o.body.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SLet ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SLet {
    #[pyo3(get)]
    pub var_name: Py<Name>,
    #[pyo3(get)]
    pub var_value: PyObject,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SLet {
    #[new]
    #[pyo3(signature = (var_name, var_value, body, loc = None))]
    fn py_new(
        py: Python<'_>,
        var_name: Py<Name>,
        var_value: PyObject,
        body: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, STerm) {
        (SLet { var_name, var_value, body, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["var_name", "var_value", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "(let {} = {} in\n\t{})",
            self.var_name.borrow(py).__str__(),
            self.var_value.bind(py).str()?,
            self.body.bind(py).str()?
        ))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SLet>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.var_name.borrow(py);
                let b = o.var_name.borrow(py);
                Ok(a.name == b.name
                    && a.id == b.id
                    && self.var_value.bind(py).eq(o.var_value.bind(py))?
                    && self.body.bind(py).eq(o.body.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SRec ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SRec {
    #[pyo3(get)]
    pub var_name: Py<Name>,
    #[pyo3(get)]
    pub var_type: PyObject,
    #[pyo3(get)]
    pub var_value: PyObject,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub decreasing_by: Py<PyTuple>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SRec {
    #[new]
    #[pyo3(signature = (var_name, var_type, var_value, body, decreasing_by = None, loc = None))]
    fn py_new(
        py: Python<'_>,
        var_name: Py<Name>,
        var_type: PyObject,
        var_value: PyObject,
        body: PyObject,
        decreasing_by: Option<Py<PyTuple>>,
        loc: Option<PyObject>,
    ) -> (Self, STerm) {
        let decreasing_by = decreasing_by.unwrap_or_else(|| PyTuple::empty_bound(py).unbind());
        (
            SRec { var_name, var_type, var_value, body, decreasing_by, loc: resolve_loc(py, loc) },
            STerm,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["var_name", "var_type", "var_value", "body", "decreasing_by", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "(let {} : {} = {} in\n\t{})",
            self.var_name.borrow(py).__str__(),
            self.var_type.bind(py).str()?,
            self.var_value.bind(py).str()?,
            self.body.bind(py).str()?
        ))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SRec>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.var_name.borrow(py);
                let b = o.var_name.borrow(py);
                Ok(a.name == b.name
                    && a.id == b.id
                    && self.var_type.bind(py).eq(o.var_type.bind(py))?
                    && self.var_value.bind(py).eq(o.var_value.bind(py))?
                    && self.body.bind(py).eq(o.body.bind(py))?
                    && self.decreasing_by.bind(py).eq(o.decreasing_by.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SIf ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SIf {
    #[pyo3(get)]
    pub cond: PyObject,
    #[pyo3(get)]
    pub then: PyObject,
    #[pyo3(get)]
    pub otherwise: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SIf {
    #[new]
    #[pyo3(signature = (cond, then, otherwise, loc = None))]
    fn py_new(
        py: Python<'_>,
        cond: PyObject,
        then: PyObject,
        otherwise: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, STerm) {
        (SIf { cond, then, otherwise, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["cond", "then", "otherwise", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "(if {} then {} else {})",
            self.cond.bind(py).str()?,
            self.then.bind(py).str()?,
            self.otherwise.bind(py).str()?
        ))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<SIf>() {
            Ok(o) => {
                let o = o.borrow();
                Ok(self.cond.bind(py).eq(o.cond.bind(py))?
                    && self.then.bind(py).eq(o.then.bind(py))?
                    && self.otherwise.bind(py).eq(o.otherwise.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SAnonConstructor ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SAnonConstructor {
    #[pyo3(get)]
    pub name: String,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SAnonConstructor {
    #[new]
    #[pyo3(signature = (name, loc = None))]
    fn py_new(py: Python<'_>, name: String, loc: Option<PyObject>) -> (Self, STerm) {
        (SAnonConstructor { name, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "loc"])
    }

    fn __str__(&self) -> String {
        format!(".{}", self.name)
    }

    fn __repr__(&self) -> String {
        format!("AnonCtor(.{})", self.name)
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<SAnonConstructor>() {
            Ok(o) => o.borrow().name == self.name,
            Err(_) => false,
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SMatchBranch (standalone dataclass, not an STerm) ----
#[pyclass(module = "aeon_rs", frozen)]
pub struct SMatchBranch {
    #[pyo3(get)]
    pub constructor: Py<Name>,
    #[pyo3(get)]
    pub binders: Py<PyList>,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub qualifier: Option<String>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SMatchBranch {
    #[new]
    #[pyo3(signature = (constructor, binders, body, qualifier = None, loc = None))]
    fn py_new(
        py: Python<'_>,
        constructor: Py<Name>,
        binders: Py<PyList>,
        body: PyObject,
        qualifier: Option<String>,
        loc: Option<PyObject>,
    ) -> Self {
        SMatchBranch { constructor, binders, body, qualifier, loc: resolve_loc(py, loc) }
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["constructor", "binders", "body", "qualifier", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let l = self.binders.bind(py);
        let mut bs: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            bs.push(l.get_item(i)?.str()?.to_string());
        }
        let binders = bs.join(" ");
        let prefix = match &self.qualifier {
            Some(q) => format!("{}.", q),
            None => String::new(),
        };
        let cons = self.constructor.borrow(py).__str__();
        if binders.is_empty() {
            Ok(format!("| {}{} => {}", prefix, cons, self.body.bind(py).str()?))
        } else {
            Ok(format!("| {}{} {} => {}", prefix, cons, binders, self.body.bind(py).str()?))
        }
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SMatch ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SMatch {
    #[pyo3(get)]
    pub scrutinee: PyObject,
    #[pyo3(get)]
    pub branches: Py<PyList>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SMatch {
    #[new]
    #[pyo3(signature = (scrutinee, branches, loc = None))]
    fn py_new(py: Python<'_>, scrutinee: PyObject, branches: Py<PyList>, loc: Option<PyObject>) -> (Self, STerm) {
        (SMatch { scrutinee, branches, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["scrutinee", "branches", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let l = self.branches.bind(py);
        let mut bs: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            bs.push(l.get_item(i)?.str()?.to_string());
        }
        Ok(format!("(match {} with\n{})", self.scrutinee.bind(py).str()?, bs.join("\n")))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- STypeAbstraction ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct STypeAbstraction {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub kind: PyObject,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl STypeAbstraction {
    #[new]
    #[pyo3(signature = (name, kind, body, loc = None))]
    fn py_new(py: Python<'_>, name: Py<Name>, kind: PyObject, body: PyObject, loc: Option<PyObject>) -> (Self, STerm) {
        (STypeAbstraction { name, kind, body, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "kind", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "ƛ{}:{}.({})",
            self.name.borrow(py).__str__(),
            self.kind.bind(py).str()?,
            self.body.bind(py).str()?
        ))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SRefinementAbstraction ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SRefinementAbstraction {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub sort: PyObject,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SRefinementAbstraction {
    #[new]
    #[pyo3(signature = (name, sort, body, loc = None))]
    fn py_new(py: Python<'_>, name: Py<Name>, sort: PyObject, body: PyObject, loc: Option<PyObject>) -> (Self, STerm) {
        (SRefinementAbstraction { name, sort, body, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "sort", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "Λ<{}:{} -> Bool>=> ({})",
            self.name.borrow(py).__str__(),
            self.sort.bind(py).str()?,
            self.body.bind(py).str()?
        ))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- STypeApplication (NOT frozen in Python — keep mutable getters only) ----
#[pyclass(module = "aeon_rs", extends = STerm)]
pub struct STypeApplication {
    #[pyo3(get, set)]
    pub body: PyObject,
    #[pyo3(get, set, name = "type")]
    pub type_: PyObject,
    #[pyo3(get, set)]
    pub loc: PyObject,
}

#[pymethods]
impl STypeApplication {
    #[new]
    #[pyo3(signature = (body, r#type, loc = None))]
    fn py_new(py: Python<'_>, body: PyObject, r#type: PyObject, loc: Option<PyObject>) -> (Self, STerm) {
        (STypeApplication { body, type_: r#type, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["body", "type", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!("({})[{}]", self.body.bind(py).str()?, self.type_.bind(py).str()?))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// ---- SRefinementApplication ----
#[pyclass(module = "aeon_rs", extends = STerm, frozen)]
pub struct SRefinementApplication {
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub refinement: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl SRefinementApplication {
    #[new]
    #[pyo3(signature = (body, refinement, loc = None))]
    fn py_new(py: Python<'_>, body: PyObject, refinement: PyObject, loc: Option<PyObject>) -> (Self, STerm) {
        (SRefinementApplication { body, refinement, loc: resolve_loc(py, loc) }, STerm)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["body", "refinement", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!("({})[{}]", self.body.bind(py).str()?, self.refinement.bind(py).str()?))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.as_any())
    }
}

// =========================================================================
// Node hierarchy (declarations, definitions, program)
// =========================================================================

#[pyclass(module = "aeon_rs", subclass)]
pub struct Node;

#[pymethods]
impl Node {
    #[new]
    fn py_new() -> Self {
        Node
    }
}

#[pyclass(module = "aeon_rs", extends = Node)]
pub struct ImportAe {
    #[pyo3(get, set)]
    pub module_path: String,
    #[pyo3(get, set)]
    pub selected_names: Py<PyList>,
    #[pyo3(get, set)]
    pub is_open: bool,
    #[pyo3(get, set)]
    pub loc: PyObject,
}

#[pymethods]
impl ImportAe {
    #[new]
    #[pyo3(signature = (module_path, selected_names = None, is_open = false, loc = None))]
    fn py_new(
        py: Python<'_>,
        module_path: String,
        selected_names: Option<Py<PyList>>,
        is_open: bool,
        loc: Option<PyObject>,
    ) -> (Self, Node) {
        let selected_names = selected_names.unwrap_or_else(|| PyList::empty_bound(py).unbind());
        (
            ImportAe { module_path, selected_names, is_open, loc: resolve_loc(py, loc) },
            Node,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["module_path", "selected_names", "is_open", "loc"])
    }

    #[getter]
    fn file_path(&self) -> String {
        format!("{}.ae", self.module_path.replace('.', "/"))
    }

    #[getter]
    fn module_name(&self) -> String {
        self.module_path.split('.').next().unwrap_or("").to_string()
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        if self.is_open {
            Ok(format!("open {};", self.module_path))
        } else {
            let l = self.selected_names.bind(py);
            if l.len() > 0 {
                let mut ns: Vec<String> = Vec::with_capacity(l.len());
                for i in 0..l.len() {
                    ns.push(l.get_item(i)?.str()?.to_string());
                }
                Ok(format!("import {} ({});", self.module_path, ns.join(", ")))
            } else {
                Ok(format!("import {};", self.module_path))
            }
        }
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }
}

#[pyclass(module = "aeon_rs", extends = Node)]
pub struct TypeDecl {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set)]
    pub args: Py<PyList>,
    #[pyo3(get, set)]
    pub loc: PyObject,
}

#[pymethods]
impl TypeDecl {
    #[new]
    #[pyo3(signature = (name, args = None, loc = None))]
    fn py_new(py: Python<'_>, name: Py<Name>, args: Option<Py<PyList>>, loc: Option<PyObject>) -> (Self, Node) {
        let args = args.unwrap_or_else(|| PyList::empty_bound(py).unbind());
        (TypeDecl { name, args, loc: resolve_loc(py, loc) }, Node)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "args", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> String {
        format!("type {};", self.name.borrow(py).__str__())
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        self.__str__(py)
    }
}

#[pyclass(module = "aeon_rs", extends = Node)]
pub struct InductiveDecl {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set)]
    pub args: Py<PyList>,
    #[pyo3(get, set)]
    pub rforalls: Py<PyList>,
    #[pyo3(get, set)]
    pub constructors: Py<PyList>,
    #[pyo3(get, set)]
    pub measures: Py<PyList>,
    #[pyo3(get, set)]
    pub loc: PyObject,
}

#[pymethods]
impl InductiveDecl {
    #[new]
    #[pyo3(signature = (name, args = None, rforalls = None, constructors = None, measures = None, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        args: Option<Py<PyList>>,
        rforalls: Option<Py<PyList>>,
        constructors: Option<Py<PyList>>,
        measures: Option<Py<PyList>>,
        loc: Option<PyObject>,
    ) -> (Self, Node) {
        let mk = || PyList::empty_bound(py).unbind();
        (
            InductiveDecl {
                name,
                args: args.unwrap_or_else(mk),
                rforalls: rforalls.unwrap_or_else(mk),
                constructors: constructors.unwrap_or_else(mk),
                measures: measures.unwrap_or_else(mk),
                loc: resolve_loc(py, loc),
            },
            Node,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "args", "rforalls", "constructors", "measures", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let argl = self.args.bind(py);
        let mut args: Vec<String> = Vec::with_capacity(argl.len());
        for i in 0..argl.len() {
            args.push(argl.get_item(i)?.str()?.to_string());
        }
        let head = if args.is_empty() {
            format!("inductive {}", self.name.borrow(py).__str__())
        } else {
            format!("inductive {} {}", self.name.borrow(py).__str__(), args.join(" "))
        };
        Ok(head)
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }
}

#[pyclass(module = "aeon_rs", extends = Node)]
pub struct Decorator {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set)]
    pub macro_args: Py<PyList>,
    #[pyo3(get, set)]
    pub named_args: PyObject, // dict[Name, STerm]
    #[pyo3(get, set)]
    pub loc: PyObject,
}

#[pymethods]
impl Decorator {
    #[new]
    #[pyo3(signature = (name, macro_args, named_args = None, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        macro_args: Py<PyList>,
        named_args: Option<PyObject>,
        loc: Option<PyObject>,
    ) -> (Self, Node) {
        let named_args = named_args.unwrap_or_else(|| pyo3::types::PyDict::new_bound(py).into());
        (Decorator { name, macro_args, named_args, loc: resolve_loc(py, loc) }, Node)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "macro_args", "named_args", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let l = self.macro_args.bind(py);
        let mut ma: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            ma.push(l.get_item(i)?.str()?.to_string());
        }
        Ok(format!("@{}({})", self.name.borrow(py).__str__(), ma.join(", ")))
    }
}

#[pyclass(module = "aeon_rs", extends = Node)]
pub struct Definition {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set)]
    pub foralls: Py<PyList>,
    #[pyo3(get, set)]
    pub args: Py<PyList>,
    #[pyo3(get, set, name = "type")]
    pub type_: PyObject,
    #[pyo3(get, set)]
    pub body: PyObject,
    #[pyo3(get, set)]
    pub decorators: Py<PyList>,
    #[pyo3(get, set)]
    pub rforalls: Py<PyList>,
    #[pyo3(get, set)]
    pub decreasing_by: Py<PyList>,
    #[pyo3(get, set)]
    pub loc: PyObject,
}

#[pymethods]
impl Definition {
    #[new]
    #[pyo3(signature = (name, foralls, args, r#type, body, decorators = None, rforalls = None, decreasing_by = None, loc = None))]
    #[allow(clippy::too_many_arguments)]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        foralls: Py<PyList>,
        args: Py<PyList>,
        r#type: PyObject,
        body: PyObject,
        decorators: Option<Py<PyList>>,
        rforalls: Option<Py<PyList>>,
        decreasing_by: Option<Py<PyList>>,
        loc: Option<PyObject>,
    ) -> PyResult<(Self, Node)> {
        // __post_init__: assert isinstance(self.type, SType)
        if !r#type.bind(py).is_instance_of::<SType>() {
            return Err(pyo3::exceptions::PyAssertionError::new_err(
                "Definition.type must be an SType",
            ));
        }
        let mk = || PyList::empty_bound(py).unbind();
        Ok((
            Definition {
                name,
                foralls,
                args,
                type_: r#type,
                body,
                decorators: decorators.unwrap_or_else(mk),
                rforalls: rforalls.unwrap_or_else(mk),
                decreasing_by: decreasing_by.unwrap_or_else(mk),
                loc: resolve_loc(py, loc),
            },
            Node,
        ))
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(
            py,
            &["name", "foralls", "args", "type", "body", "decorators", "rforalls", "decreasing_by", "loc"],
        )
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let args = self.args.bind(py);
        if args.len() == 0 {
            Ok(format!(
                "def {} : {} = {};",
                self.name.borrow(py).__str__(),
                self.type_.bind(py).str()?,
                self.body.bind(py).str()?
            ))
        } else {
            let mut parts: Vec<String> = Vec::with_capacity(args.len());
            for i in 0..args.len() {
                let tup = args.get_item(i)?;
                let n = tup.get_item(0)?.str()?.to_string();
                let t = tup.get_item(1)?.str()?.to_string();
                parts.push(format!("{}:{}", n, t));
            }
            Ok(format!(
                "def {} {} : {} {{\n {} \n}}",
                self.name.borrow(py).__str__(),
                parts.join(", "),
                self.type_.bind(py).str()?,
                self.body.bind(py).str()?
            ))
        }
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }
}

#[pyclass(module = "aeon_rs", extends = Node)]
pub struct Program {
    #[pyo3(get, set)]
    pub imports: Py<PyList>,
    #[pyo3(get, set)]
    pub type_decls: Py<PyList>,
    #[pyo3(get, set)]
    pub inductive_decls: Py<PyList>,
    #[pyo3(get, set)]
    pub definitions: Py<PyList>,
}

#[pymethods]
impl Program {
    #[new]
    fn py_new(
        imports: Py<PyList>,
        type_decls: Py<PyList>,
        inductive_decls: Py<PyList>,
        definitions: Py<PyList>,
    ) -> (Self, Node) {
        (Program { imports, type_decls, inductive_decls, definitions }, Node)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["imports", "type_decls", "inductive_decls", "definitions"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        fn join(py: Python<'_>, l: &Py<PyList>) -> PyResult<String> {
            let l = l.bind(py);
            let mut parts: Vec<String> = Vec::with_capacity(l.len());
            for i in 0..l.len() {
                parts.push(l.get_item(i)?.str()?.to_string());
            }
            Ok(parts.join("\n"))
        }
        Ok(format!(
            "{}\n{}\n{}\n{}",
            join(py, &self.imports)?,
            join(py, &self.type_decls)?,
            join(py, &self.inductive_decls)?,
            join(py, &self.definitions)?
        ))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }
}
