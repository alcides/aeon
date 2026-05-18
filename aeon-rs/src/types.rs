//! Type hierarchy. Mirrors aeon.core.types.

use pyo3::prelude::*;
use pyo3::types::PyTuple;
use std::hash::{Hash, Hasher};

use crate::loc::resolve_loc;
use crate::name::Name;

// ---------- Base class ----------

#[pyclass(module = "aeon_rs", subclass)]
pub struct Type;

#[pymethods]
impl Type {
    #[new]
    fn py_new() -> Self {
        Type
    }
}

// ---------- Top ----------

#[pyclass(module = "aeon_rs", extends = Type, frozen)]
pub struct Top;

#[pymethods]
impl Top {
    #[new]
    fn py_new() -> (Self, Type) {
        (Top, Type)
    }

    fn __repr__(&self) -> &'static str {
        "⊤"
    }

    fn __str__(&self) -> &'static str {
        "⊤"
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other.is_instance_of::<Top>()
    }

    fn __hash__(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        let mut h = DefaultHasher::new();
        "Top".hash(&mut h);
        h.finish()
    }
}

// ---------- TypeVar ----------

#[pyclass(module = "aeon_rs", extends = Type, frozen)]
pub struct TypeVar {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl TypeVar {
    #[new]
    #[pyo3(signature = (name, loc = None))]
    fn py_new(py: Python<'_>, name: Py<Name>, loc: Option<PyObject>) -> PyResult<(Self, Type)> {
        {
            let n = name.borrow(py);
            if n.name == "Int" || n.name == "Bool" {
                return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                    "TypeVar('{}') is not allowed; use TypeConstructor instead",
                    n.name
                )));
            }
        }
        Ok((TypeVar { name, loc: resolve_loc(py, loc) }, Type))
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        self.name.borrow(py).__str__()
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<TypeVar>() {
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
}

// ---------- AbstractionType ----------

pub fn default_multiplicity(py: Python<'_>) -> PyObject {
    crate::multiplicity::momega(py)
}

#[pyclass(module = "aeon_rs", extends = Type, frozen)]
pub struct AbstractionType {
    #[pyo3(get)]
    pub var_name: Py<Name>,
    #[pyo3(get)]
    pub var_type: PyObject,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
    #[pyo3(get)]
    pub multiplicity: PyObject,
}

#[pymethods]
impl AbstractionType {
    #[new]
    #[pyo3(signature = (var_name, var_type, r#type, loc = None, multiplicity = None))]
    fn py_new(
        py: Python<'_>,
        var_name: Py<Name>,
        var_type: PyObject,
        r#type: PyObject,
        loc: Option<PyObject>,
        multiplicity: Option<PyObject>,
    ) -> (Self, Type) {
        let multiplicity = multiplicity.unwrap_or_else(|| default_multiplicity(py));
        (
            AbstractionType {
                var_name,
                var_type,
                type_: r#type,
                loc: resolve_loc(py, loc),
                multiplicity,
            },
            Type,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["var_name", "var_type", "type", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let v = self.var_name.borrow(py).__str__();
        let vt = self.var_type.bind(py).repr()?.to_string();
        let t = self.type_.bind(py).repr()?.to_string();
        Ok(format!("({}:{}) -> {}", v, vt, t))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<AbstractionType>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.var_name.borrow(py);
                let b = o.var_name.borrow(py);
                if !(a.name == b.name && a.id == b.id) {
                    return Ok(false);
                }
                if !self.var_type.bind(py).eq(o.var_type.bind(py))? {
                    return Ok(false);
                }
                if !self.type_.bind(py).eq(o.type_.bind(py))? {
                    return Ok(false);
                }
                Ok(true)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        let mut h = DefaultHasher::new();
        let n = self.var_name.borrow(py);
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        let h1: isize = self.var_type.bind(py).hash()?;
        let h2: isize = self.type_.bind(py).hash()?;
        h1.hash(&mut h);
        h2.hash(&mut h);
        Ok(h.finish())
    }
}

// ---------- RefinedType ----------

#[pyclass(module = "aeon_rs", extends = Type, frozen)]
pub struct RefinedType {
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
impl RefinedType {
    #[new]
    #[pyo3(signature = (name, r#type, refinement, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        r#type: PyObject,
        refinement: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Type) {
        (
            RefinedType {
                name,
                type_: r#type,
                refinement,
                loc: resolve_loc(py, loc),
            },
            Type,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "type", "refinement", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let n = self.name.borrow(py).__str__();
        let t = self.type_.bind(py).repr()?.to_string();
        let r = self.refinement.bind(py).repr()?.to_string();
        Ok(format!("{{ {}:{} | {} }}", n, t, r))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<RefinedType>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                if !(a.name == b.name && a.id == b.id) {
                    return Ok(false);
                }
                if !self.type_.bind(py).eq(o.type_.bind(py))? {
                    return Ok(false);
                }
                if !self.refinement.bind(py).eq(o.refinement.bind(py))? {
                    return Ok(false);
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
        let h1: isize = self.type_.bind(py).hash()?;
        let h2: isize = self.refinement.bind(py).hash()?;
        h1.hash(&mut h);
        h2.hash(&mut h);
        Ok(h.finish())
    }
}

// ---------- TypePolymorphism ----------

#[pyclass(module = "aeon_rs", extends = Type, frozen)]
pub struct TypePolymorphism {
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
impl TypePolymorphism {
    #[new]
    #[pyo3(signature = (name, kind, body, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        kind: PyObject,
        body: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Type) {
        (
            TypePolymorphism { name, kind, body, loc: resolve_loc(py, loc) },
            Type,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "kind", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let n = self.name.borrow(py).__str__();
        let k = self.kind.bind(py).repr()?.to_string();
        let b = self.body.bind(py).repr()?.to_string();
        Ok(format!("forall {}:{}, {}", n, k, b))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<TypePolymorphism>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                if !(a.name == b.name && a.id == b.id) {
                    return Ok(false);
                }
                if !self.kind.bind(py).eq(o.kind.bind(py))? {
                    return Ok(false);
                }
                if !self.body.bind(py).eq(o.body.bind(py))? {
                    return Ok(false);
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
        let h1: isize = self.kind.bind(py).hash()?;
        let h2: isize = self.body.bind(py).hash()?;
        h1.hash(&mut h);
        h2.hash(&mut h);
        Ok(h.finish())
    }
}

// ---------- RefinementPolymorphism ----------

#[pyclass(module = "aeon_rs", extends = Type, frozen)]
pub struct RefinementPolymorphism {
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
impl RefinementPolymorphism {
    #[new]
    #[pyo3(signature = (name, sort, body, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        sort: PyObject,
        body: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Type) {
        (
            RefinementPolymorphism { name, sort, body, loc: resolve_loc(py, loc) },
            Type,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "sort", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let n = self.name.borrow(py).__str__();
        let s = self.sort.bind(py).repr()?.to_string();
        let b = self.body.bind(py).repr()?.to_string();
        Ok(format!("forall <{}:{} -> Bool>, {}", n, s, b))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<RefinementPolymorphism>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.name.borrow(py);
                let b = o.name.borrow(py);
                if !(a.name == b.name && a.id == b.id) {
                    return Ok(false);
                }
                if !self.sort.bind(py).eq(o.sort.bind(py))? {
                    return Ok(false);
                }
                if !self.body.bind(py).eq(o.body.bind(py))? {
                    return Ok(false);
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
        let h1: isize = self.sort.bind(py).hash()?;
        let h2: isize = self.body.bind(py).hash()?;
        h1.hash(&mut h);
        h2.hash(&mut h);
        Ok(h.finish())
    }
}

// ---------- TypeConstructor ----------

#[pyclass(module = "aeon_rs", extends = Type, frozen)]
pub struct TypeConstructor {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub args: Py<pyo3::types::PyList>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl TypeConstructor {
    #[new]
    #[pyo3(signature = (name, args = None, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        args: Option<Py<pyo3::types::PyList>>,
        loc: Option<PyObject>,
    ) -> (Self, Type) {
        let args = args.unwrap_or_else(|| pyo3::types::PyList::empty_bound(py).unbind());
        (
            TypeConstructor { name, args, loc: resolve_loc(py, loc) },
            Type,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "args", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let n = self.name.borrow(py).__str__();
        let l = self.args.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            parts.push(l.get_item(i)?.str()?.to_string());
        }
        Ok(format!("{} {}", n, parts.join(", ")))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<TypeConstructor>() {
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

// ---------- ExistentialType ----------
//
// Form B: a type wrapped with a list of existential binders.
// `binders`: tuple of (Name, Type) pairs. `body`: bare type — never another
// ExistentialType (binders are flat). Mirrors aeon.core.types.ExistentialType.

#[pyclass(module = "aeon_rs", extends = Type, frozen)]
pub struct ExistentialType {
    #[pyo3(get)]
    pub binders: Py<PyTuple>,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl ExistentialType {
    #[new]
    #[pyo3(signature = (binders, body, loc = None))]
    fn py_new(
        py: Python<'_>,
        binders: Py<PyTuple>,
        body: PyObject,
        loc: Option<PyObject>,
    ) -> PyResult<(Self, Type)> {
        // __post_init__: body must not be another ExistentialType.
        if body.bind(py).is_instance_of::<ExistentialType>() {
            return Err(pyo3::exceptions::PyAssertionError::new_err(
                "ExistentialType bodies must be flat; flatten via `with_binders`.",
            ));
        }
        Ok((ExistentialType { binders, body, loc: resolve_loc(py, loc) }, Type))
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["binders", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let bs = self.binders.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(bs.len());
        for i in 0..bs.len() {
            let tup = bs.get_item(i)?;
            let n = tup.get_item(0)?.str()?.to_string();
            let t = tup.get_item(1)?.str()?.to_string();
            parts.push(format!("{}:{}", n, t));
        }
        Ok(format!("[{}] {}", parts.join("; "), self.body.bind(py).str()?))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<ExistentialType>() {
            Ok(o) => {
                let o = o.borrow();
                Ok(self.binders.bind(py).eq(o.binders.bind(py))?
                    && self.body.bind(py).eq(o.body.bind(py))?)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        let mut h = DefaultHasher::new();
        let bh: isize = self.binders.bind(py).hash()?;
        let bodyh: isize = self.body.bind(py).hash()?;
        bh.hash(&mut h);
        bodyh.hash(&mut h);
        Ok(h.finish())
    }
}
