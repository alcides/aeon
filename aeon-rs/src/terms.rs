//! Term hierarchy. Mirrors aeon.core.terms.

use pyo3::prelude::*;
use pyo3::types::PyTuple;
use std::hash::{Hash, Hasher};

use crate::loc::resolve_loc;
use crate::name::Name;

// Base term hash matches Python: hash(str(self))
fn hash_via_str(py: Python<'_>, obj: &Bound<'_, PyAny>) -> PyResult<u64> {
    let s = obj.str()?.to_string();
    use std::collections::hash_map::DefaultHasher;
    let mut h = DefaultHasher::new();
    s.hash(&mut h);
    Ok(h.finish())
}

// ---------- Base class ----------

#[pyclass(module = "aeon_rs", subclass)]
pub struct Term;

#[pymethods]
impl Term {
    #[new]
    fn py_new() -> Self {
        Term
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        let py = slf.py();
        hash_via_str(py, slf.as_any())
    }

    fn pretty(&self) {}
}

// ---------- Literal ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct Literal {
    #[pyo3(get)]
    pub value: PyObject,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl Literal {
    #[new]
    #[pyo3(signature = (value, r#type, loc = None))]
    fn py_new(
        py: Python<'_>,
        value: PyObject,
        r#type: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Term) {
        (
            Literal { value, type_: r#type, loc: resolve_loc(py, loc) },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["value", "type", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        // Detect t_string by checking if type repr is "String "
        let trepr = self.type_.bind(py).str()?.to_string();
        let val = self.value.bind(py).str()?.to_string();
        if trepr.starts_with("String ") || trepr == "String" {
            Ok(format!("\"{}\"", val))
        } else {
            Ok(val.to_lowercase())
        }
    }

    fn pretty(&self, py: Python<'_>) -> PyResult<String> {
        self.__repr__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<Literal>() {
            Ok(o) => {
                let o = o.borrow();
                if !self.value.bind(py).eq(o.value.bind(py))? {
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

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- Var ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct Var {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl Var {
    #[new]
    #[pyo3(signature = (name, loc = None))]
    fn py_new(py: Python<'_>, name: Py<Name>, loc: Option<PyObject>) -> (Self, Term) {
        (Var { name, loc: resolve_loc(py, loc) }, Term)
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

    fn pretty(&self, py: Python<'_>) -> String {
        self.name.borrow(py).pretty()
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<Var>() {
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
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- Annotation ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct Annotation {
    #[pyo3(get)]
    pub expr: PyObject,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl Annotation {
    #[new]
    #[pyo3(signature = (expr, r#type, loc = None))]
    fn py_new(
        py: Python<'_>,
        expr: PyObject,
        r#type: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Term) {
        (
            Annotation { expr, type_: r#type, loc: resolve_loc(py, loc) },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["expr", "type", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let e = self.expr.bind(py).str()?.to_string();
        let t = self.type_.bind(py).str()?.to_string();
        Ok(format!("({} : {})", e, t))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<Annotation>() {
            Ok(o) => {
                let o = o.borrow();
                if !self.expr.bind(py).eq(o.expr.bind(py))? {
                    return Ok(false);
                }
                Ok(true)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- Hole ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct Hole {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl Hole {
    #[new]
    #[pyo3(signature = (name, loc = None))]
    fn py_new(py: Python<'_>, name: Py<Name>, loc: Option<PyObject>) -> (Self, Term) {
        (Hole { name, loc: resolve_loc(py, loc) }, Term)
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
        match other.downcast::<Hole>() {
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
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- Application ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct Application {
    #[pyo3(get)]
    pub fun: PyObject,
    #[pyo3(get)]
    pub arg: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl Application {
    #[new]
    #[pyo3(signature = (fun, arg, loc = None))]
    fn py_new(
        py: Python<'_>,
        fun: PyObject,
        arg: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Term) {
        (
            Application { fun, arg, loc: resolve_loc(py, loc) },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["fun", "arg", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let f = self.fun.bind(py).str()?.to_string();
        let a = self.arg.bind(py).str()?.to_string();
        Ok(format!("({} {})", f, a))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<Application>() {
            Ok(o) => {
                let o = o.borrow();
                if !self.fun.bind(py).eq(o.fun.bind(py))? {
                    return Ok(false);
                }
                if !self.arg.bind(py).eq(o.arg.bind(py))? {
                    return Ok(false);
                }
                Ok(true)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- Abstraction ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct Abstraction {
    #[pyo3(get)]
    pub var_name: Py<Name>,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl Abstraction {
    #[new]
    #[pyo3(signature = (var_name, body, loc = None))]
    fn py_new(
        py: Python<'_>,
        var_name: Py<Name>,
        body: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Term) {
        (
            Abstraction { var_name, body, loc: resolve_loc(py, loc) },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["var_name", "body", "loc"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let vn = self.var_name.borrow(py).__str__();
        let b = self.body.bind(py).str()?.to_string();
        Ok(format!("(\\{} -> {})", vn, b))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<Abstraction>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.var_name.borrow(py);
                let b = o.var_name.borrow(py);
                if !(a.name == b.name && a.id == b.id) {
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

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- Let ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct Let {
    #[pyo3(get)]
    pub var_name: Py<Name>,
    #[pyo3(get)]
    pub var_value: PyObject,
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
    #[pyo3(get)]
    pub multiplicity: PyObject,
}

#[pymethods]
impl Let {
    #[new]
    #[pyo3(signature = (var_name, var_value, body, loc = None, multiplicity = None))]
    fn py_new(
        py: Python<'_>,
        var_name: Py<Name>,
        var_value: PyObject,
        body: PyObject,
        loc: Option<PyObject>,
        multiplicity: Option<PyObject>,
    ) -> (Self, Term) {
        let multiplicity = multiplicity.unwrap_or_else(|| crate::types::default_multiplicity(py));
        (
            Let {
                var_name,
                var_value,
                body,
                loc: resolve_loc(py, loc),
                multiplicity,
            },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["var_name", "var_value", "body", "loc", "multiplicity"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let vn = self.var_name.borrow(py).__str__();
        let vv = self.var_value.bind(py).str()?.to_string();
        let b = self.body.bind(py).str()?.to_string();
        Ok(format!("(let {} = {} in\n\t{})", vn, vv, b))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<Let>() {
            Ok(o) => {
                let o = o.borrow();
                let a = self.var_name.borrow(py);
                let b = o.var_name.borrow(py);
                if !(a.name == b.name && a.id == b.id) {
                    return Ok(false);
                }
                if !self.var_value.bind(py).eq(o.var_value.bind(py))? {
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

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- Rec ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct Rec {
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
    #[pyo3(get)]
    pub multiplicity: PyObject,
}

#[pymethods]
impl Rec {
    #[new]
    #[pyo3(signature = (var_name, var_type, var_value, body, decreasing_by = None, loc = None, multiplicity = None))]
    fn py_new(
        py: Python<'_>,
        var_name: Py<Name>,
        var_type: PyObject,
        var_value: PyObject,
        body: PyObject,
        decreasing_by: Option<Py<PyTuple>>,
        loc: Option<PyObject>,
        multiplicity: Option<PyObject>,
    ) -> (Self, Term) {
        let decreasing_by = decreasing_by
            .unwrap_or_else(|| PyTuple::empty_bound(py).unbind());
        let multiplicity = multiplicity.unwrap_or_else(|| crate::types::default_multiplicity(py));
        (
            Rec {
                var_name,
                var_type,
                var_value,
                body,
                decreasing_by,
                loc: resolve_loc(py, loc),
                multiplicity,
            },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(
            py,
            &[
                "var_name",
                "var_type",
                "var_value",
                "body",
                "decreasing_by",
                "loc",
                "multiplicity",
            ],
        )
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let vn = self.var_name.borrow(py).__str__();
        let vt = self.var_type.bind(py).str()?.to_string();
        let vv = self.var_value.bind(py).str()?.to_string();
        let b = self.body.bind(py).str()?.to_string();
        Ok(format!("(let {} : {} = {} in\n\t{})", vn, vt, vv, b))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<Rec>() {
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
                if !self.var_value.bind(py).eq(o.var_value.bind(py))? {
                    return Ok(false);
                }
                if !self.body.bind(py).eq(o.body.bind(py))? {
                    return Ok(false);
                }
                if !self.decreasing_by.bind(py).eq(o.decreasing_by.bind(py))? {
                    return Ok(false);
                }
                Ok(true)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- If ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct If {
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
impl If {
    #[new]
    #[pyo3(signature = (cond, then, otherwise, loc = None))]
    fn py_new(
        py: Python<'_>,
        cond: PyObject,
        then: PyObject,
        otherwise: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Term) {
        (
            If { cond, then, otherwise, loc: resolve_loc(py, loc) },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["cond", "then", "otherwise", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let c = self.cond.bind(py).str()?.to_string();
        let t = self.then.bind(py).str()?.to_string();
        let o = self.otherwise.bind(py).str()?.to_string();
        Ok(format!("(if {} then {} else {})", c, t, o))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<If>() {
            Ok(o) => {
                let o = o.borrow();
                if !self.cond.bind(py).eq(o.cond.bind(py))? {
                    return Ok(false);
                }
                if !self.then.bind(py).eq(o.then.bind(py))? {
                    return Ok(false);
                }
                if !self.otherwise.bind(py).eq(o.otherwise.bind(py))? {
                    return Ok(false);
                }
                Ok(true)
            }
            Err(_) => Ok(false),
        }
    }

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- TypeAbstraction ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct TypeAbstraction {
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
impl TypeAbstraction {
    #[new]
    #[pyo3(signature = (name, kind, body, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        kind: PyObject,
        body: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Term) {
        (
            TypeAbstraction { name, kind, body, loc: resolve_loc(py, loc) },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "kind", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let n = self.name.borrow(py).__str__();
        let k = self.kind.bind(py).str()?.to_string();
        let b = self.body.bind(py).str()?.to_string();
        Ok(format!("ƛ{}:{}.({})", n, k, b))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<TypeAbstraction>() {
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

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- RefinementAbstraction ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct RefinementAbstraction {
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
impl RefinementAbstraction {
    #[new]
    #[pyo3(signature = (name, sort, body, loc = None))]
    fn py_new(
        py: Python<'_>,
        name: Py<Name>,
        sort: PyObject,
        body: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Term) {
        (
            RefinementAbstraction { name, sort, body, loc: resolve_loc(py, loc) },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "sort", "body", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let n = self.name.borrow(py).__str__();
        let s = self.sort.bind(py).str()?.to_string();
        let b = self.body.bind(py).str()?.to_string();
        Ok(format!("Λρ{}:({}).({})", n, s, b))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<RefinementAbstraction>() {
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

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- TypeApplication ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct TypeApplication {
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl TypeApplication {
    #[new]
    #[pyo3(signature = (body, r#type, loc = None))]
    fn py_new(
        py: Python<'_>,
        body: PyObject,
        r#type: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Term) {
        (
            TypeApplication { body, type_: r#type, loc: resolve_loc(py, loc) },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["body", "type", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let b = self.body.bind(py).str()?.to_string();
        let t = self.type_.bind(py).str()?.to_string();
        Ok(format!("({})[{}]", b, t))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<TypeApplication>() {
            Ok(o) => {
                let o = o.borrow();
                if !self.body.bind(py).eq(o.body.bind(py))? {
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

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}

// ---------- RefinementApplication ----------

#[pyclass(module = "aeon_rs", extends = Term, frozen)]
pub struct RefinementApplication {
    #[pyo3(get)]
    pub body: PyObject,
    #[pyo3(get)]
    pub refinement: PyObject,
    #[pyo3(get)]
    pub loc: PyObject,
}

#[pymethods]
impl RefinementApplication {
    #[new]
    #[pyo3(signature = (body, refinement, loc = None))]
    fn py_new(
        py: Python<'_>,
        body: PyObject,
        refinement: PyObject,
        loc: Option<PyObject>,
    ) -> (Self, Term) {
        (
            RefinementApplication { body, refinement, loc: resolve_loc(py, loc) },
            Term,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["body", "refinement", "loc"])
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let b = self.body.bind(py).str()?.to_string();
        let r = self.refinement.bind(py).str()?.to_string();
        Ok(format!("({})[{}]", b, r))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        self.__str__(py)
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        match other.downcast::<RefinementApplication>() {
            Ok(o) => {
                let o = o.borrow();
                if !self.body.bind(py).eq(o.body.bind(py))? {
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

    fn __hash__(slf: &Bound<'_, Self>) -> PyResult<u64> {
        hash_via_str(slf.py(), slf.as_any())
    }
}
