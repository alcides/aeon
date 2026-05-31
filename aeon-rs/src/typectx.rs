//! Typing context (`TypingContext`) and its binder entries.
//!
//! Direct port of `aeon.typechecking.context`. The context is just a list of
//! `TypingContextEntry`s (`VariableBinder`, `UninterpretedBinder`,
//! `ReflectedBinder`, `TypeBinder`, `TypeConstructorBinder`); the type checker
//! reads it backwards (newest entries first).

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::kind::Kind;
use crate::name::Name;
use crate::types::{
    AbstractionType, RefinedType, Top, Type, TypeConstructor, TypePolymorphism, TypeVar,
};

// =============================================================================
// TypingContextEntry — abstract base class.
// =============================================================================

#[pyclass(module = "aeon_rs", subclass)]
pub struct TypingContextEntry;

#[pymethods]
impl TypingContextEntry {
    #[new]
    fn py_new() -> Self {
        TypingContextEntry
    }
}

// =============================================================================
// VariableBinder
// =============================================================================

#[pyclass(module = "aeon_rs", extends = TypingContextEntry, frozen)]
pub struct VariableBinder {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
}

#[pymethods]
impl VariableBinder {
    #[new]
    fn py_new(name: Py<Name>, r#type: PyObject) -> (Self, TypingContextEntry) {
        (VariableBinder { name, type_: r#type }, TypingContextEntry)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "type"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "{} : {}",
            self.name.bind(py).str()?,
            self.type_.bind(py).str()?
        ))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        let Ok(o) = other.downcast::<VariableBinder>() else {
            return Ok(false);
        };
        let o = o.borrow();
        let a = self.name.borrow(py);
        let b = o.name.borrow(py);
        Ok(a.name == b.name && a.id == b.id && self.type_.bind(py).eq(o.type_.bind(py))?)
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        let n = self.name.borrow(py);
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        let th: isize = self.type_.bind(py).hash()?;
        th.hash(&mut h);
        Ok(h.finish())
    }
}

// =============================================================================
// UninterpretedBinder
// =============================================================================

#[pyclass(module = "aeon_rs", extends = TypingContextEntry, frozen)]
pub struct UninterpretedBinder {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
}

#[pymethods]
impl UninterpretedBinder {
    #[new]
    fn py_new(name: Py<Name>, r#type: PyObject) -> (Self, TypingContextEntry) {
        (UninterpretedBinder { name, type_: r#type }, TypingContextEntry)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "type"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "uninterpreted {} : {}",
            self.name.bind(py).str()?,
            self.type_.bind(py).str()?
        ))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        let Ok(o) = other.downcast::<UninterpretedBinder>() else {
            return Ok(false);
        };
        let o = o.borrow();
        let a = self.name.borrow(py);
        let b = o.name.borrow(py);
        Ok(a.name == b.name && a.id == b.id && self.type_.bind(py).eq(o.type_.bind(py))?)
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        let n = self.name.borrow(py);
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        let th: isize = self.type_.bind(py).hash()?;
        th.hash(&mut h);
        Ok(h.finish())
    }
}

// =============================================================================
// ReflectedBinder
// =============================================================================

#[pyclass(module = "aeon_rs", extends = TypingContextEntry, frozen)]
pub struct ReflectedBinder {
    #[pyo3(get)]
    pub name: Py<Name>,
    #[pyo3(get, name = "type")]
    pub type_: PyObject,
    #[pyo3(get)]
    pub params: Py<PyTuple>,
    #[pyo3(get)]
    pub body: PyObject,
}

#[pymethods]
impl ReflectedBinder {
    #[new]
    fn py_new(
        name: Py<Name>,
        r#type: PyObject,
        params: Py<PyTuple>,
        body: PyObject,
    ) -> (Self, TypingContextEntry) {
        (
            ReflectedBinder { name, type_: r#type, params, body },
            TypingContextEntry,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "type", "params", "body"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let p = self.params.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(p.len());
        for i in 0..p.len() {
            parts.push(p.get_item(i)?.str()?.to_string());
        }
        Ok(format!(
            "reflected {}({}) : {}",
            self.name.bind(py).str()?,
            parts.join(", "),
            self.type_.bind(py).str()?
        ))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        let Ok(o) = other.downcast::<ReflectedBinder>() else {
            return Ok(false);
        };
        let o = o.borrow();
        let a = self.name.borrow(py);
        let b = o.name.borrow(py);
        Ok(a.name == b.name
            && a.id == b.id
            && self.type_.bind(py).eq(o.type_.bind(py))?
            && self.params.bind(py).eq(o.params.bind(py))?
            && self.body.bind(py).eq(o.body.bind(py))?)
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        let n = self.name.borrow(py);
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        let th: isize = self.type_.bind(py).hash()?;
        th.hash(&mut h);
        let ph: isize = self.params.bind(py).hash()?;
        ph.hash(&mut h);
        let bh: isize = self.body.bind(py).hash()?;
        bh.hash(&mut h);
        Ok(h.finish())
    }
}

// =============================================================================
// TypeBinder
// =============================================================================

#[pyclass(module = "aeon_rs", extends = TypingContextEntry, frozen)]
pub struct TypeBinder {
    #[pyo3(get)]
    pub type_name: Py<Name>,
    #[pyo3(get)]
    pub type_kind: PyObject,
}

#[pymethods]
impl TypeBinder {
    #[new]
    #[pyo3(signature = (type_name, type_kind = None))]
    fn py_new(
        py: Python<'_>,
        type_name: Py<Name>,
        type_kind: Option<PyObject>,
    ) -> PyResult<(Self, TypingContextEntry)> {
        let kind = match type_kind {
            Some(k) => k,
            None => crate::kind::star(py),
        };
        Ok((TypeBinder { type_name, type_kind: kind }, TypingContextEntry))
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["type_name", "type_kind"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "type {} {}",
            self.type_name.bind(py).str()?,
            self.type_kind.bind(py).str()?
        ))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        let Ok(o) = other.downcast::<TypeBinder>() else {
            return Ok(false);
        };
        let o = o.borrow();
        let a = self.type_name.borrow(py);
        let b = o.type_name.borrow(py);
        Ok(a.name == b.name
            && a.id == b.id
            && self.type_kind.bind(py).eq(o.type_kind.bind(py))?)
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        let n = self.type_name.borrow(py);
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        let kh: isize = self.type_kind.bind(py).hash()?;
        kh.hash(&mut h);
        Ok(h.finish())
    }
}

// =============================================================================
// TypeConstructorBinder
// =============================================================================

#[pyclass(module = "aeon_rs", extends = TypingContextEntry)]
pub struct TypeConstructorBinder {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    /// Inductive-type formal parameter list (e.g. `["T", "U"]` for
    /// `type Pair(T, U)`). Empty for plain `type Foo;`.
    #[pyo3(get, set)]
    pub args: Py<PyList>,
}

#[pymethods]
impl TypeConstructorBinder {
    #[new]
    fn py_new(name: Py<Name>, args: Py<PyList>) -> (Self, TypingContextEntry) {
        (TypeConstructorBinder { name, args }, TypingContextEntry)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "args"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let a = self.args.bind(py);
        let args_str = if a.len() == 0 {
            String::new()
        } else {
            let mut parts: Vec<String> = Vec::with_capacity(a.len());
            for i in 0..a.len() {
                parts.push(a.get_item(i)?.str()?.to_string());
            }
            format!("({})", parts.join(", "))
        };
        Ok(format!("type {}{}", self.name.bind(py).str()?, args_str))
    }

    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        let Ok(o) = other.downcast::<TypeConstructorBinder>() else {
            return Ok(false);
        };
        let o = o.borrow();
        let a = self.name.borrow(py);
        let b = o.name.borrow(py);
        Ok(a.name == b.name && a.id == b.id && self.args.bind(py).eq(o.args.bind(py))?)
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        let n = self.name.borrow(py);
        n.name.hash(&mut h);
        n.id.hash(&mut h);
        let a = self.args.bind(py);
        for i in 0..a.len() {
            let item_hash: isize = a.get_item(i)?.hash()?;
            item_hash.hash(&mut h);
        }
        Ok(h.finish())
    }
}

// =============================================================================
// TypingContext
// =============================================================================

#[pyclass(module = "aeon_rs")]
pub struct TypingContext {
    #[pyo3(get, set)]
    pub entries: Py<PyList>,
}

#[pymethods]
impl TypingContext {
    #[new]
    #[pyo3(signature = (entries = None))]
    fn py_new(py: Python<'_>, entries: Option<Py<PyList>>) -> PyResult<Self> {
        let entries = match entries {
            Some(e) => e,
            None => PyList::empty_bound(py).unbind(),
        };
        // Inject the built-in core types as TypeConstructorBinder entries —
        // mirrors Python's `__post_init__`.
        let core_types_mod = py.import_bound("aeon.core.types")?;
        let builtin = core_types_mod.getattr("builtin_core_types")?;
        let builtin_list = builtin.downcast::<PyList>()?;
        let entries_b = entries.bind(py);
        for i in (0..builtin_list.len()).rev() {
            let tc = builtin_list.get_item(i)?;
            let name_attr = tc.getattr("name")?;
            let name: Py<Name> = name_attr.downcast::<Name>()?.clone().unbind();
            let empty = PyList::empty_bound(py).unbind();
            let binder = Py::new(
                py,
                (TypeConstructorBinder { name, args: empty }, TypingContextEntry),
            )?;
            // Check membership before inserting.
            let mut found = false;
            for j in 0..entries_b.len() {
                let e = entries_b.get_item(j)?;
                if e.eq(binder.clone_ref(py))? {
                    found = true;
                    break;
                }
            }
            if !found {
                entries_b.insert(0, binder)?;
            }
        }
        Ok(TypingContext { entries })
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["entries"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let e = self.entries.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(e.len());
        for i in 0..e.len() {
            parts.push(e.get_item(i)?.repr()?.to_string());
        }
        Ok(format!("[[{}]]", parts.join("; ")))
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<u64> {
        let e = self.entries.bind(py);
        let mut total: i64 = 0;
        for i in 0..e.len() {
            let item_hash: isize = e.get_item(i)?.hash()?;
            total = total.wrapping_add(item_hash as i64);
        }
        Ok(total as u64)
    }

    pub fn with_var(&self, py: Python<'_>, name: Py<Name>, r#type: PyObject) -> PyResult<TypingContext> {
        let new_entries = PyList::empty_bound(py);
        let e = self.entries.bind(py);
        for i in 0..e.len() {
            new_entries.append(e.get_item(i)?)?;
        }
        let v = Py::new(
            py,
            (VariableBinder { name, type_: r#type }, TypingContextEntry),
        )?;
        new_entries.append(v)?;
        Ok(TypingContext { entries: new_entries.unbind() })
    }

    pub fn with_typevar(&self, py: Python<'_>, name: Py<Name>, kind: PyObject) -> PyResult<TypingContext> {
        let new_entries = PyList::empty_bound(py);
        let e = self.entries.bind(py);
        for i in 0..e.len() {
            new_entries.append(e.get_item(i)?)?;
        }
        let v = Py::new(
            py,
            (TypeBinder { type_name: name, type_kind: kind }, TypingContextEntry),
        )?;
        new_entries.append(v)?;
        Ok(TypingContext { entries: new_entries.unbind() })
    }

    pub fn type_of(&self, py: Python<'_>, name: Py<Name>) -> PyResult<PyObject> {
        let e = self.entries.bind(py);
        let target = name.borrow(py);
        for i in 0..e.len() {
            let item = e.get_item(i)?;
            if let Ok(vb) = item.downcast::<VariableBinder>() {
                let vb = vb.borrow();
                let n = vb.name.borrow(py);
                if n.name == target.name && n.id == target.id {
                    return Ok(vb.type_.clone_ref(py));
                }
            }
        }
        Ok(py.None())
    }

    pub fn kind_of(&self, py: Python<'_>, ty: PyObject) -> PyResult<PyObject> {
        let bound = ty.bind(py);
        let base_kind = || -> PyResult<PyObject> { Ok(crate::kind::base(py)) };
        let star_kind = || -> PyResult<PyObject> { Ok(crate::kind::star(py)) };

        if bound.is_instance_of::<Top>() {
            return base_kind();
        }
        if let Ok(rt) = bound.downcast::<RefinedType>() {
            let rt = rt.borrow();
            let inner = rt.type_.bind(py);
            if inner.is_instance_of::<TypeConstructor>() {
                return base_kind();
            }
            if let Ok(tv) = inner.downcast::<TypeVar>() {
                let tv = tv.borrow();
                let nm = tv.name.borrow(py);
                let tvs = self.typevars(py)?;
                let tvs_b = tvs.bind(py);
                let mut found = false;
                for i in 0..tvs_b.len() {
                    let tup = tvs_b.get_item(i)?;
                    let entry_name = tup.get_item(0)?.downcast::<Name>()?.borrow();
                    if entry_name.name == nm.name && entry_name.id == nm.id {
                        found = true;
                        break;
                    }
                }
                assert!(found, "TypeVar in RefinedType not in context typevars");
                return base_kind();
            }
        }
        if let Ok(tv) = bound.downcast::<TypeVar>() {
            let tv = tv.borrow();
            let nm = tv.name.borrow(py);
            let tvs = self.typevars(py)?;
            let tvs_b = tvs.bind(py);
            let mut found = false;
            for i in 0..tvs_b.len() {
                let tup = tvs_b.get_item(i)?;
                let entry_name = tup.get_item(0)?.downcast::<Name>()?.borrow();
                if entry_name.name == nm.name && entry_name.id == nm.id {
                    found = true;
                    break;
                }
            }
            assert!(found, "TypeVar not in context typevars");
            return base_kind();
        }
        if bound.is_instance_of::<AbstractionType>() || bound.is_instance_of::<TypePolymorphism>() {
            return star_kind();
        }
        if bound.is_instance_of::<TypeConstructor>() {
            return base_kind();
        }
        Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "Unknown type in context: {}",
            bound.repr()?.to_string()
        )))
    }

    pub fn typevars(&self, py: Python<'_>) -> PyResult<Py<PyList>> {
        let out = PyList::empty_bound(py);
        let e = self.entries.bind(py);
        for i in 0..e.len() {
            let item = e.get_item(i)?;
            if let Ok(tb) = item.downcast::<TypeBinder>() {
                let tb = tb.borrow();
                let tup = PyTuple::new_bound(
                    py,
                    &[
                        tb.type_name.clone_ref(py).into_any(),
                        tb.type_kind.clone_ref(py),
                    ],
                );
                out.append(tup)?;
            }
        }
        Ok(out.unbind())
    }

    pub fn vars(&self, py: Python<'_>) -> PyResult<Py<PyList>> {
        let out = PyList::empty_bound(py);
        let e = self.entries.bind(py);
        for i in 0..e.len() {
            let item = e.get_item(i)?;
            if let Ok(vb) = item.downcast::<VariableBinder>() {
                let vb = vb.borrow();
                let tup = PyTuple::new_bound(
                    py,
                    &[vb.name.clone_ref(py).into_any(), vb.type_.clone_ref(py)],
                );
                out.append(tup)?;
            } else if let Ok(ub) = item.downcast::<UninterpretedBinder>() {
                let ub = ub.borrow();
                let tup = PyTuple::new_bound(
                    py,
                    &[ub.name.clone_ref(py).into_any(), ub.type_.clone_ref(py)],
                );
                out.append(tup)?;
            } else if let Ok(rb) = item.downcast::<ReflectedBinder>() {
                let rb = rb.borrow();
                let tup = PyTuple::new_bound(
                    py,
                    &[rb.name.clone_ref(py).into_any(), rb.type_.clone_ref(py)],
                );
                out.append(tup)?;
            }
        }
        Ok(out.unbind())
    }

    fn concrete_vars(&self, py: Python<'_>) -> PyResult<Py<PyList>> {
        let out = PyList::empty_bound(py);
        let e = self.entries.bind(py);
        for i in 0..e.len() {
            let item = e.get_item(i)?;
            if let Ok(vb) = item.downcast::<VariableBinder>() {
                let vb = vb.borrow();
                let tup = PyTuple::new_bound(
                    py,
                    &[vb.name.clone_ref(py).into_any(), vb.type_.clone_ref(py)],
                );
                out.append(tup)?;
            }
        }
        Ok(out.unbind())
    }

    fn has_uninterpreted_fun(&self, py: Python<'_>, name: Py<Name>) -> PyResult<bool> {
        let target = name.borrow(py);
        let e = self.entries.bind(py);
        for i in 0..e.len() {
            let item = e.get_item(i)?;
            if let Ok(ub) = item.downcast::<UninterpretedBinder>() {
                let ub = ub.borrow();
                let n = ub.name.borrow(py);
                if n.name == target.name && n.id == target.id {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    pub fn get_type_constructor(&self, py: Python<'_>, name: Py<Name>) -> PyResult<PyObject> {
        let target = name.borrow(py);
        let e = self.entries.bind(py);
        for i in (0..e.len()).rev() {
            let item = e.get_item(i)?;
            if let Ok(tcb) = item.downcast::<TypeConstructorBinder>() {
                let tcb = tcb.borrow();
                let ename = tcb.name.borrow(py);
                if ename.name == target.name && ename.id == target.id {
                    return Ok(tcb.args.clone_ref(py).into_any());
                }
            }
        }
        if matches!(target.name.as_str(), "Unit" | "Int" | "Bool" | "Float" | "String") {
            return Ok(PyList::empty_bound(py).into_any().unbind());
        }
        Ok(py.None())
    }
}
