//! Decorator infrastructure — port of `aeon.decorators.api` and
//! `aeon.decorators.__init__`.
//!
//! The *dispatching* (sugar vs core partitioning, sugar-phase invocation
//! loop, core-phase queue, queue-drain pass) lives in Rust. The actual
//! decorator functions (e.g. `minimize`, `csv_data`, `after_typecheck`)
//! remain Python — Rust looks them up in
//! `aeon.decorators.sugar_decorators_environment` and
//! `aeon.synthesis.core_decorators.core_decorators_environment` at call
//! time and invokes them via FFI.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};
use std::sync::OnceLock;

use crate::name::Name;
use crate::sugar::{Decorator, Definition};

// ---- CORE_DECORATOR_QUEUE_META_KEY singleton ---------------------------

static CORE_DECORATOR_QUEUE_META_KEY: OnceLock<PyObject> = OnceLock::new();

fn core_decorator_queue_key(py: Python<'_>) -> PyObject {
    if let Some(obj) = CORE_DECORATOR_QUEUE_META_KEY.get() {
        return obj.clone_ref(py);
    }
    let n = Py::new(
        py,
        Name { name: "_aeon_core_decorator_queue".to_string(), id: -1 },
    )
    .expect("Name allocation")
    .into_any();
    let _ = CORE_DECORATOR_QUEUE_META_KEY.set(n.clone_ref(py));
    n
}

#[pyfunction]
pub fn get_core_decorator_queue_meta_key(py: Python<'_>) -> PyObject {
    core_decorator_queue_key(py)
}

// ---- metadata_update / metadata_update_by_name ------------------------

/// `metadata_update(metadata, fun, aux_dict=None)` — store/extend
/// `metadata[fun.name]` with `aux_dict`. Mutates `metadata` in place
/// and also returns it (matching the Python contract).
#[pyfunction]
#[pyo3(signature = (metadata, fun, aux_dict = None))]
pub fn metadata_update(
    py: Python<'_>,
    metadata: Py<PyDict>,
    fun: PyObject,
    aux_dict: Option<Py<PyDict>>,
) -> PyResult<Py<PyDict>> {
    let aux = aux_dict.unwrap_or_else(|| PyDict::new_bound(py).unbind());
    // Duck-type: any object with a `.name` attribute that's a Name.
    let fname_obj = fun.bind(py).getattr("name")?;
    let fname: Py<Name> = fname_obj.downcast::<Name>()?.clone().unbind();
    update_md(py, &metadata, &fname, &aux)?;
    Ok(metadata)
}

/// `metadata_update_by_name(metadata, fname, aux_dict=None)`.
#[pyfunction]
#[pyo3(signature = (metadata, fname, aux_dict = None))]
pub fn metadata_update_by_name(
    py: Python<'_>,
    metadata: Py<PyDict>,
    fname: Py<Name>,
    aux_dict: Option<Py<PyDict>>,
) -> PyResult<Py<PyDict>> {
    let aux = aux_dict.unwrap_or_else(|| PyDict::new_bound(py).unbind());
    update_md(py, &metadata, &fname, &aux)?;
    Ok(metadata)
}

fn update_md(
    py: Python<'_>,
    metadata: &Py<PyDict>,
    fname: &Py<Name>,
    aux: &Py<PyDict>,
) -> PyResult<()> {
    let md_b = metadata.bind(py);
    if let Some(existing) = md_b.get_item(fname.clone_ref(py))? {
        // existing.update(aux)
        let existing_dict = existing.downcast::<PyDict>()?;
        for (k, v) in aux.bind(py).iter() {
            existing_dict.set_item(k, v)?;
        }
    } else {
        md_b.set_item(fname.clone_ref(py), aux.clone_ref(py))?;
    }
    Ok(())
}

// ---- apply_decorators -------------------------------------------------

fn env_dict(py: Python<'_>, module: &str, attr: &str) -> PyResult<Py<PyDict>> {
    let m = py.import_bound(module)?;
    let d = m.getattr(attr)?;
    Ok(d.downcast::<PyDict>()?.clone().unbind())
}

fn sugar_env(py: Python<'_>) -> PyResult<Py<PyDict>> {
    env_dict(py, "aeon.decorators", "sugar_decorators_environment")
}

fn core_env(py: Python<'_>) -> PyResult<Py<PyDict>> {
    env_dict(py, "aeon.synthesis.core_decorators", "core_decorators_environment")
}

/// `apply_decorators(fun, metadata)`. Partitions `fun.decorators` into
/// sugar vs core decorators (using the two registries in Python),
/// builds a new Definition that keeps only the core decorators on the
/// node, and invokes each sugar decorator in order. Each invocation
/// returns `(new_def, extra_defs, new_metadata)`.
#[pyfunction]
pub fn apply_decorators(
    py: Python<'_>,
    fun: Py<Definition>,
    metadata: Option<Py<PyDict>>,
) -> PyResult<(Py<Definition>, Py<PyList>, Py<PyDict>)> {
    let metadata = metadata.unwrap_or_else(|| PyDict::new_bound(py).unbind());

    let sugar = sugar_env(py)?;
    let core = core_env(py)?;
    let sugar_b = sugar.bind(py);
    let core_b = core.bind(py);

    // Partition decorators.
    let decorators = fun.borrow(py).decorators.clone_ref(py);
    let fun_name_str = fun.borrow(py).name.borrow(py).name.clone();
    let dec_b = decorators.bind(py);
    let sugar_decs = PyList::empty_bound(py);
    let core_decs = PyList::empty_bound(py);
    for i in 0..dec_b.len() {
        let dec_any = dec_b.get_item(i)?;
        let dec: Py<Decorator> = dec_any.downcast::<Decorator>()?.clone().unbind();
        let dname = dec.borrow(py).name.borrow(py).name.clone();
        let in_sugar = sugar_b.contains(&dname)?;
        let in_core = core_b.contains(&dname)?;
        if in_sugar {
            sugar_decs.append(dec)?;
        } else if in_core {
            core_decs.append(dec)?;
        } else {
            return Err(pyo3::exceptions::PyException::new_err(format!(
                "Unknown decorator named {}, in function {}.",
                dname, fun_name_str,
            )));
        }
    }

    // Build the "partial" Definition: same fields except decorators=core_decs.
    let f = fun.borrow(py);
    let mut partial = Py::new(
        py,
        (
            Definition {
                name: f.name.clone_ref(py),
                foralls: f.foralls.clone_ref(py),
                args: f.args.clone_ref(py),
                type_: f.type_.clone_ref(py),
                body: f.body.clone_ref(py),
                decorators: core_decs.unbind(),
                rforalls: f.rforalls.clone_ref(py),
                decreasing_by: f.decreasing_by.clone_ref(py),
                arg_multiplicities: f.arg_multiplicities.clone_ref(py),
                loc: f.loc.clone_ref(py),
            },
            crate::sugar::Node,
        ),
    )?;
    drop(f);

    // Iterate sugar decorators in order, calling each Python processor.
    let total_extra = PyList::empty_bound(py);
    let mut metadata = metadata;

    let sugar_decs_iter = partial.borrow(py).decorators.clone_ref(py); // placeholder no-op
    let _ = sugar_decs_iter; // suppress unused — we iterate via sugar_decs below.

    // Re-read sugar_decs (we moved it into the list above).
    // We need a fresh iterator since sugar_decs.unbind() was consumed.
    // Instead, partition again into a Rust Vec at the start. Simpler: redo
    // the partitioning a second time, but only for sugar.
    let decorators = fun.borrow(py).decorators.clone_ref(py);
    let dec_b = decorators.bind(py);
    let mut sugar_list: Vec<Py<Decorator>> = Vec::new();
    for i in 0..dec_b.len() {
        let dec_any = dec_b.get_item(i)?;
        let dec: Py<Decorator> = dec_any.downcast::<Decorator>()?.clone().unbind();
        let dname = dec.borrow(py).name.borrow(py).name.clone();
        if sugar_b.contains(&dname)? {
            sugar_list.push(dec);
        }
    }

    for dec in sugar_list {
        let dname = dec.borrow(py).name.borrow(py).name.clone();
        let processor = sugar_b
            .get_item(&dname)?
            .ok_or_else(|| pyo3::exceptions::PyKeyError::new_err(dname.clone()))?;
        let result = processor.call1((
            dec.clone_ref(py),
            partial.clone_ref(py),
            metadata.clone_ref(py),
        ))?;
        // Unpack (partial, extra, metadata).
        let new_partial: Py<Definition> = result
            .get_item(0)?
            .downcast::<Definition>()?
            .clone()
            .unbind();
        let extra: Py<PyList> = result.get_item(1)?.downcast::<PyList>()?.clone().unbind();
        let new_md: Py<PyDict> = result.get_item(2)?.downcast::<PyDict>()?.clone().unbind();

        partial = new_partial;
        metadata = new_md;
        let extra_b = extra.bind(py);
        for j in 0..extra_b.len() {
            total_extra.append(extra_b.get_item(j)?)?;
        }
    }

    Ok((partial, total_extra.unbind(), metadata))
}

// ---- collect_core_decorator_queue -------------------------------------

/// Move core-phase decorators from each definition into
/// `metadata[CORE_DECORATOR_QUEUE_META_KEY]`, leaving the definition
/// with `decorators=[]`.
#[pyfunction]
pub fn collect_core_decorator_queue(
    py: Python<'_>,
    definitions: Py<PyList>,
    metadata: Py<PyDict>,
) -> PyResult<(Py<PyList>, Py<PyDict>)> {
    let key = core_decorator_queue_key(py);
    let core = core_env(py)?;
    let core_b = core.bind(py);

    // queue: list[tuple[Name, Decorator]] — read existing from metadata if any.
    let md_b = metadata.bind(py);
    let queue = PyList::empty_bound(py);
    if let Some(existing) = md_b.get_item(key.clone_ref(py))? {
        if !existing.is_none() {
            let existing_list = existing.downcast::<PyList>()?;
            for i in 0..existing_list.len() {
                queue.append(existing_list.get_item(i)?)?;
            }
        }
    }

    let new_definitions = PyList::empty_bound(py);
    let defs_b = definitions.bind(py);
    for i in 0..defs_b.len() {
        let d_any = defs_b.get_item(i)?;
        let d: Py<Definition> = d_any.downcast::<Definition>()?.clone().unbind();
        let db = d.borrow(py);
        let decorators = db.decorators.clone_ref(py);
        let dec_b = decorators.bind(py);
        for j in 0..dec_b.len() {
            let dec_any = dec_b.get_item(j)?;
            let dec: Py<Decorator> = dec_any.downcast::<Decorator>()?.clone().unbind();
            let dname = dec.borrow(py).name.borrow(py).name.clone();
            if !core_b.contains(&dname)? {
                return Err(pyo3::exceptions::PyValueError::new_err(format!(
                    "Unexpected decorator {:?} on function {:?} (expected only core-phase decorators at this stage).",
                    dname,
                    db.name.borrow(py).name,
                )));
            }
            let entry = PyTuple::new_bound(py, [db.name.clone_ref(py).into_any(), dec.into_any()]);
            queue.append(entry)?;
        }
        // Build new Definition with decorators=[].
        let new_d = Py::new(
            py,
            (
                Definition {
                    name: db.name.clone_ref(py),
                    foralls: db.foralls.clone_ref(py),
                    args: db.args.clone_ref(py),
                    type_: db.type_.clone_ref(py),
                    body: db.body.clone_ref(py),
                    decorators: PyList::empty_bound(py).unbind(),
                    rforalls: db.rforalls.clone_ref(py),
                    decreasing_by: db.decreasing_by.clone_ref(py),
                    arg_multiplicities: db.arg_multiplicities.clone_ref(py),
                    loc: db.loc.clone_ref(py),
                },
                crate::sugar::Node,
            ),
        )?;
        drop(db);
        new_definitions.append(new_d)?;
    }

    // md = dict(metadata); md[CORE_DECORATOR_QUEUE_META_KEY] = queue
    let new_md = PyDict::new_bound(py);
    for (k, v) in md_b.iter() {
        new_md.set_item(k, v)?;
    }
    new_md.set_item(key, queue.unbind())?;

    Ok((new_definitions.unbind(), new_md.unbind()))
}

// ---- apply_core_decorators_phase --------------------------------------

/// Drain the core-decorator queue stored in `metadata` and call each
/// registered Python core decorator.
#[pyfunction]
pub fn apply_core_decorators_phase(
    py: Python<'_>,
    typing_ctx: PyObject,
    core_program: PyObject,
    metadata: Py<PyDict>,
) -> PyResult<Py<PyDict>> {
    let key = core_decorator_queue_key(py);
    let md_b = metadata.bind(py);
    let queue_obj = md_b.get_item(key.clone_ref(py))?;
    // pop the entry from the metadata dict (mirrors Python's `.pop(...)`)
    if md_b.contains(key.clone_ref(py))? {
        md_b.del_item(key.clone_ref(py))?;
    }
    let queue = match queue_obj {
        Some(o) if !o.is_none() => {
            let l = o.downcast::<PyList>()?;
            (0..l.len())
                .map(|i| l.get_item(i))
                .collect::<PyResult<Vec<_>>>()?
        }
        _ => return Ok(metadata),
    };

    if queue.is_empty() {
        return Ok(metadata);
    }

    let core = core_env(py)?;
    let core_b = core.bind(py);

    let mut md = metadata;
    for entry in queue {
        let fname = entry.get_item(0)?.unbind();
        let dec = entry.get_item(1)?.unbind();
        let dname = dec.bind(py).getattr("name")?.getattr("name")?.extract::<String>()?;
        let proc = core_b
            .get_item(&dname)?
            .ok_or_else(|| pyo3::exceptions::PyKeyError::new_err(dname.clone()))?;
        let result = proc.call1((
            dec,
            fname,
            typing_ctx.clone_ref(py),
            core_program.clone_ref(py),
            md.clone_ref(py),
        ))?;
        md = result.downcast::<PyDict>()?.clone().unbind();
    }
    Ok(md)
}
