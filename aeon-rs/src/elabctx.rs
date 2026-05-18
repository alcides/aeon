//! Elaboration-phase typing context (port of `aeon.elaboration.context`).

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};

use crate::name::Name;

#[pyclass(module = "aeon_rs", subclass)]
pub struct ElabTypingContextEntry;

#[pymethods]
impl ElabTypingContextEntry {
    #[new]
    fn py_new() -> Self {
        ElabTypingContextEntry
    }
}

#[pyclass(module = "aeon_rs", extends = ElabTypingContextEntry)]
pub struct ElabVariableBinder {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set, name = "type")]
    pub type_: PyObject,
}

#[pymethods]
impl ElabVariableBinder {
    #[new]
    fn py_new(name: Py<Name>, r#type: PyObject) -> (Self, ElabTypingContextEntry) {
        (ElabVariableBinder { name, type_: r#type }, ElabTypingContextEntry)
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
}

#[pyclass(module = "aeon_rs", extends = ElabTypingContextEntry)]
pub struct ElabUninterpretedBinder {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set, name = "type")]
    pub type_: PyObject,
}

#[pymethods]
impl ElabUninterpretedBinder {
    #[new]
    fn py_new(name: Py<Name>, r#type: PyObject) -> (Self, ElabTypingContextEntry) {
        (
            ElabUninterpretedBinder { name, type_: r#type },
            ElabTypingContextEntry,
        )
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
}

#[pyclass(module = "aeon_rs", extends = ElabTypingContextEntry)]
pub struct ElabTypeVarBinder {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    /// Python `Kind` — held by reference, not introspected here.
    #[pyo3(get, set, name = "type")]
    pub type_: PyObject,
}

#[pymethods]
impl ElabTypeVarBinder {
    #[new]
    fn py_new(name: Py<Name>, r#type: PyObject) -> (Self, ElabTypingContextEntry) {
        (
            ElabTypeVarBinder { name, type_: r#type },
            ElabTypingContextEntry,
        )
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "type"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "typevar {} : {}",
            self.name.bind(py).str()?,
            self.type_.bind(py).str()?
        ))
    }
}

#[pyclass(module = "aeon_rs", extends = ElabTypingContextEntry)]
pub struct ElabTypeDecl {
    #[pyo3(get, set)]
    pub name: Py<Name>,
    #[pyo3(get, set)]
    pub args: Py<PyList>,
}

#[pymethods]
impl ElabTypeDecl {
    #[new]
    fn py_new(name: Py<Name>, args: Py<PyList>) -> (Self, ElabTypingContextEntry) {
        (ElabTypeDecl { name, args }, ElabTypingContextEntry)
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["name", "args"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let a = self.args.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(a.len());
        for i in 0..a.len() {
            parts.push(a.get_item(i)?.str()?.to_string());
        }
        Ok(format!(
            "type {}({})",
            self.name.bind(py).str()?,
            parts.join(", ")
        ))
    }
}

#[pyclass(module = "aeon_rs")]
pub struct ElaborationTypingContext {
    #[pyo3(get, set)]
    pub entries: Py<PyList>,
    #[pyo3(get, set)]
    pub constructor_to_type: Py<PyDict>,
    #[pyo3(get, set)]
    pub constructor_defs: Py<PyDict>,
}

#[pymethods]
impl ElaborationTypingContext {
    #[new]
    #[pyo3(signature = (entries = None, constructor_to_type = None, constructor_defs = None))]
    fn py_new(
        py: Python<'_>,
        entries: Option<Py<PyList>>,
        constructor_to_type: Option<Py<PyDict>>,
        constructor_defs: Option<Py<PyDict>>,
    ) -> Self {
        let entries = entries.unwrap_or_else(|| PyList::empty_bound(py).unbind());
        let constructor_to_type = constructor_to_type.unwrap_or_else(|| PyDict::new_bound(py).unbind());
        let constructor_defs = constructor_defs.unwrap_or_else(|| PyDict::new_bound(py).unbind());
        ElaborationTypingContext {
            entries,
            constructor_to_type,
            constructor_defs,
        }
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(py, &["entries", "constructor_to_type", "constructor_defs"])
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let e = self.entries.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(e.len());
        for i in 0..e.len() {
            parts.push(e.get_item(i)?.repr()?.to_string());
        }
        Ok(format!("ElaborationTypingContext({})", parts.join("; ")))
    }

    pub fn type_of(&self, py: Python<'_>, name: Py<Name>) -> PyResult<PyObject> {
        let target_name = name.borrow(py).name.clone();
        let entries = self.entries.bind(py);
        for i in (0..entries.len()).rev() {
            let entry = entries.get_item(i)?;
            if let Ok(vb) = entry.downcast::<ElabVariableBinder>() {
                let vb = vb.borrow();
                if vb.name.borrow(py).name == target_name {
                    return Ok(vb.type_.clone_ref(py));
                }
            }
        }
        Ok(py.None())
    }

    pub fn with_var(
        &self,
        py: Python<'_>,
        name: Py<Name>,
        ty: PyObject,
    ) -> PyResult<ElaborationTypingContext> {
        let new_entries = PyList::empty_bound(py);
        let e = self.entries.bind(py);
        for i in 0..e.len() {
            new_entries.append(e.get_item(i)?)?;
        }
        let binder = Py::new(
            py,
            (ElabVariableBinder { name, type_: ty }, ElabTypingContextEntry),
        )?;
        new_entries.append(binder)?;
        Ok(ElaborationTypingContext {
            entries: new_entries.unbind(),
            constructor_to_type: self.constructor_to_type.clone_ref(py),
            constructor_defs: self.constructor_defs.clone_ref(py),
        })
    }

    pub fn with_typevar(
        &self,
        py: Python<'_>,
        name: Py<Name>,
        kind: PyObject,
    ) -> PyResult<ElaborationTypingContext> {
        let new_entries = PyList::empty_bound(py);
        let e = self.entries.bind(py);
        for i in 0..e.len() {
            new_entries.append(e.get_item(i)?)?;
        }
        let binder = Py::new(
            py,
            (
                ElabTypeVarBinder { name, type_: kind },
                ElabTypingContextEntry,
            ),
        )?;
        new_entries.append(binder)?;
        Ok(ElaborationTypingContext {
            entries: new_entries.unbind(),
            constructor_to_type: self.constructor_to_type.clone_ref(py),
            constructor_defs: self.constructor_defs.clone_ref(py),
        })
    }

    pub fn fresh_typevar(&self, py: Python<'_>) -> PyResult<Py<Name>> {
        let id = crate::name::next_fresh_id(py)?;
        Py::new(py, Name { name: "tv".to_string(), id })
    }
}

#[pyfunction]
#[pyo3(signature = (ls, tdecl = None, constructor_to_type = None, constructor_defs = None))]
pub fn build_typing_context(
    py: Python<'_>,
    ls: Py<PyDict>,
    tdecl: Option<Py<PyList>>,
    constructor_to_type: Option<Py<PyDict>>,
    constructor_defs: Option<Py<PyDict>>,
) -> PyResult<ElaborationTypingContext> {
    let entries = PyList::empty_bound(py);
    // Variable binders from ls dict.
    for (k, v) in ls.bind(py).iter() {
        let name: Py<Name> = k.downcast::<Name>()?.clone().unbind();
        let ty: PyObject = v.unbind();
        let binder = Py::new(
            py,
            (
                ElabVariableBinder { name, type_: ty },
                ElabTypingContextEntry,
            ),
        )?;
        entries.append(binder)?;
    }
    // Type declarations.
    if let Some(tdecl) = tdecl {
        let td_b = tdecl.bind(py);
        for i in 0..td_b.len() {
            let td = td_b.get_item(i)?;
            let name_obj = td.getattr("name")?;
            let name: Py<Name> = name_obj.downcast::<Name>()?.clone().unbind();
            let args_obj = td.getattr("args")?;
            let args: Py<PyList> = args_obj.downcast::<PyList>()?.clone().unbind();
            let binder = Py::new(
                py,
                (ElabTypeDecl { name, args }, ElabTypingContextEntry),
            )?;
            entries.append(binder)?;
        }
    }
    Ok(ElaborationTypingContext {
        entries: entries.unbind(),
        constructor_to_type: constructor_to_type
            .unwrap_or_else(|| PyDict::new_bound(py).unbind()),
        constructor_defs: constructor_defs.unwrap_or_else(|| PyDict::new_bound(py).unbind()),
    })
}
