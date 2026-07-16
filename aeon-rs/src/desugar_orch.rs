//! Top-level desugaring orchestration — port of the residual Python
//! orchestrator from `aeon.sugar.desugar`.
//!
//! The algorithmic transforms live in `crate::desugar`; this module wires
//! them together and adds the I/O-heavy parts that previously stayed in
//! Python: the import resolver (with cache + cycle guard), the decorator
//! macro pass, and the top-level `desugar` driver.
//!
//! Two pieces still cross the FFI back into Python:
//!   * the lark-based parser, invoked via `aeon.sugar.parser.mk_parser`
//!   * the decorator macro system in `aeon.decorators`
//!
//! Everything else is native Rust.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};
use std::collections::{HashMap, HashSet};
use std::env;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use crate::desugar::{
    convert_definition_to_srec, definition_with_inferred_decreasing, determine_main_function,
    expand_inductive_decls, infer_inductive_rforall_decls, introduce_forall_in_types,
    introduce_rforall_in_types, lower_by_blocks_in_definitions, lower_match_to_inductive_rec,
    replace_concrete_types, resolve_qualified_names_in_definition,
    resolve_qualified_names_in_sterm, resolve_qualified_names_in_stype, type_of_definition,
    update_program_and_context, DesugaredProgram,
};
use crate::elabctx::{build_typing_context, ElaborationTypingContext};
use crate::name::Name;
use crate::sugar::{Definition, ImportAe, Program, SApplication, STerm, SVar, TypeDecl};

// ---- Module-level state -------------------------------------------------

/// Cache of resolved-path -> parsed `Program` (stored as a PyObject so we
/// can hold it under a Mutex; `PyObject` is Send + Sync).
type ImportCache = HashMap<PathBuf, PyObject>;
type ImportingSet = HashSet<PathBuf>;

fn import_cache() -> &'static Mutex<ImportCache> {
    static CACHE: OnceLock<Mutex<ImportCache>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

fn importing_set() -> &'static Mutex<ImportingSet> {
    static SET: OnceLock<Mutex<ImportingSet>> = OnceLock::new();
    SET.get_or_init(|| Mutex::new(HashSet::new()))
}

#[pyfunction]
pub fn clear_import_cache() {
    if let Ok(mut c) = import_cache().lock() {
        c.clear();
    }
    if let Ok(mut s) = importing_set().lock() {
        s.clear();
    }
}

// ---- Small helpers ------------------------------------------------------

/// `_is_native_import_def(d)` — true iff the definition body is a call to
/// `native_import(...)`.
fn is_native_import_def(py: Python<'_>, d: &Definition) -> PyResult<bool> {
    let body = d.body.clone_ref(py);
    let app_b = body.bind(py);
    let Ok(app) = app_b.downcast::<SApplication>() else {
        return Ok(false);
    };
    let app = app.borrow();
    let fun = app.fun.clone_ref(py);
    drop(app);
    let fun_b = fun.bind(py);
    let Ok(v) = fun_b.downcast::<SVar>() else {
        return Ok(false);
    };
    let v = v.borrow();
    let n = v.name.borrow(py);
    Ok(n.name == "native_import")
}

#[pyfunction(name = "_is_native_import_def")]
pub fn py_is_native_import_def(py: Python<'_>, d: Py<Definition>) -> PyResult<bool> {
    let d = d.borrow(py);
    is_native_import_def(py, &d)
}

/// `_bare_name(module, def_name)` — strip a `<module>_` prefix if present.
fn bare_name(module_name: &str, def_name: &str) -> String {
    let prefix = format!("{}_", module_name);
    if let Some(stripped) = def_name.strip_prefix(&prefix) {
        stripped.to_string()
    } else {
        def_name.to_string()
    }
}

#[pyfunction(name = "_bare_name")]
pub fn py_bare_name(module_name: &str, def_name: &str) -> String {
    bare_name(module_name, def_name)
}

// ---- _resolve_import ----------------------------------------------------

fn possible_containers() -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    if let Ok(cwd) = env::current_dir() {
        out.push(cwd.clone());
        out.push(cwd.join("libraries"));
    }
    if let Ok(s) = env::var("AEONPATH") {
        for part in s.split(';') {
            if !part.is_empty() {
                out.push(PathBuf::from(part));
            }
        }
    }
    out
}

/// Raise `aeon.facade.api.ImportError(importel=imp, possible_containers=...)`.
fn raise_import_error(
    py: Python<'_>,
    imp: &Py<ImportAe>,
    containers: &[PathBuf],
) -> PyErr {
    let api = match py.import_bound("aeon.facade.api") {
        Ok(m) => m,
        Err(e) => return e,
    };
    let cls = match api.getattr("ImportError") {
        Ok(c) => c,
        Err(e) => return e,
    };
    // Build the kwargs dict.
    let kwargs = PyDict::new_bound(py);
    if let Err(e) = kwargs.set_item("importel", imp.clone_ref(py)) {
        return e;
    }
    // possible_containers as a list[Path] — we just pass strings; the
    // Python error class accepts Iterable[Path].
    let containers_list = PyList::empty_bound(py);
    let path_mod = match py.import_bound("pathlib") {
        Ok(m) => m,
        Err(e) => return e,
    };
    let path_cls = match path_mod.getattr("Path") {
        Ok(c) => c,
        Err(e) => return e,
    };
    for c in containers {
        let s = c.to_string_lossy().to_string();
        match path_cls.call1((s,)) {
            Ok(p) => {
                if let Err(e) = containers_list.append(p) {
                    return e;
                }
            }
            Err(e) => return e,
        }
    }
    if let Err(e) = kwargs.set_item("possible_containers", containers_list) {
        return e;
    }
    match cls.call((), Some(&kwargs)) {
        Ok(inst) => PyErr::from_value_bound(inst),
        Err(e) => e,
    }
}

fn resolve_import(py: Python<'_>, imp: &Py<ImportAe>) -> PyResult<PyObject> {
    let imp_b = imp.borrow(py);
    // Inline of ImportAe.file_path (private in Rust because it's a Python
    // @getter): `module_path.replace('.', '/') + '.ae'`.
    let path = format!("{}.ae", imp_b.module_path.replace('.', "/"));
    drop(imp_b);

    let containers = possible_containers();
    for container in &containers {
        let file = container.join(&path);
        if !file.exists() {
            continue;
        }
        let resolved = file.canonicalize().unwrap_or(file.clone());

        // Cycle check.
        {
            let importing = importing_set().lock().expect("importing-set lock");
            if importing.contains(&resolved) {
                drop(importing);
                return Err(raise_import_error(py, imp, &containers));
            }
        }

        // Cache hit?
        {
            let cache = import_cache().lock().expect("import-cache lock");
            if let Some(obj) = cache.get(&resolved) {
                return Ok(obj.clone_ref(py));
            }
        }

        // Mark as in-progress before parsing (so cycles trip).
        {
            let mut importing = importing_set().lock().expect("importing-set lock");
            importing.insert(resolved.clone());
        }
        let result = (|| -> PyResult<PyObject> {
            let contents = std::fs::read_to_string(&file).map_err(|e| {
                pyo3::exceptions::PyIOError::new_err(format!(
                    "Could not read {}: {}",
                    file.display(),
                    e
                ))
            })?;
            // mk_parser("program", filename=str(file))
            let parser_mod = py.import_bound("aeon.sugar.parser")?;
            let mk_parser = parser_mod.getattr("mk_parser")?;
            let kwargs = PyDict::new_bound(py);
            kwargs.set_item("filename", file.to_string_lossy().to_string())?;
            let parse_fn = mk_parser.call(("program",), Some(&kwargs))?;
            let parsed = parse_fn.call1((contents,))?.unbind();
            // Cache.
            let mut cache = import_cache().lock().expect("import-cache lock");
            cache.insert(resolved.clone(), parsed.clone_ref(py));
            Ok(parsed)
        })();
        // Always remove from in-progress, success or fail.
        {
            let mut importing = importing_set().lock().expect("importing-set lock");
            importing.remove(&resolved);
        }
        return result;
    }
    Err(raise_import_error(py, imp, &containers))
}

#[pyfunction(name = "_resolve_import")]
pub fn py_resolve_import(py: Python<'_>, imp: Py<ImportAe>) -> PyResult<PyObject> {
    resolve_import(py, &imp)
}

// ---- handle_imports -----------------------------------------------------

type QualifiedScope = HashMap<(String, String), Py<Name>>;
type UnqualifiedScope = HashMap<String, Py<Name>>;

fn copy_list_into(
    py: Python<'_>,
    dest: &pyo3::Bound<'_, PyList>,
    src: &Py<PyList>,
) -> PyResult<()> {
    let b = src.bind(py);
    for i in 0..b.len() {
        dest.append(b.get_item(i)?)?;
    }
    Ok(())
}

/// Recursive import processor. Returns `(defs, type_decls, qscope, uscope)`.
fn handle_imports(
    py: Python<'_>,
    imports: Py<PyList>,
    mut defs: Py<PyList>,
    mut type_decls: Py<PyList>,
) -> PyResult<(Py<PyList>, Py<PyList>, QualifiedScope, UnqualifiedScope)> {
    let mut qualified_scope: QualifiedScope = HashMap::new();
    let mut unqualified_scope: UnqualifiedScope = HashMap::new();

    let imports_b = imports.bind(py);
    let n = imports_b.len();
    // Iterate in reverse (matches Python `imports[::-1]`).
    for i in (0..n).rev() {
        let imp_any = imports_b.get_item(i)?;
        let imp: Py<ImportAe> = imp_any.downcast::<ImportAe>()?.clone().unbind();

        let import_p = resolve_import(py, &imp)?;
        let import_p_typed: Py<Program> = import_p.bind(py).downcast::<Program>()?.clone().unbind();
        let import_p_after = expand_inductive_decls(py, import_p_typed)?;
        let import_p_after_b = import_p_after.borrow(py);
        let import_p_definitions = import_p_after_b.definitions.clone_ref(py);
        let import_p_type_decls = import_p_after_b.type_decls.clone_ref(py);
        let import_p_imports = import_p_after_b.imports.clone_ref(py);
        drop(import_p_after_b);

        let mut defs_recursive: Py<PyList> = PyList::empty_bound(py).unbind();
        let mut type_decls_recursive: Py<PyList> = PyList::empty_bound(py).unbind();
        if !import_p_imports.bind(py).is_empty() {
            let (rd, rt, rq, ru) = handle_imports(
                py,
                import_p_imports,
                import_p_definitions.clone_ref(py),
                import_p_type_decls.clone_ref(py),
            )?;
            defs_recursive = rd;
            type_decls_recursive = rt;
            for (k, v) in rq {
                qualified_scope.insert(k, v);
            }
            for (k, v) in ru {
                unqualified_scope.insert(k, v);
            }
        }

        let imp_b = imp.borrow(py);
        let module_name = imp.borrow(py).module_path.split('.').last().unwrap_or("").to_string();
        let is_open = imp_b.is_open;
        let selected_names_py = imp_b.selected_names.clone_ref(py);
        drop(imp_b);

        let selected_names: Vec<String> = {
            let l = selected_names_py.bind(py);
            (0..l.len())
                .map(|i| l.get_item(i).and_then(|x| x.extract::<String>()))
                .collect::<PyResult<Vec<_>>>()?
        };

        let prefixed_definitions = PyList::empty_bound(py);
        let import_p_defs_b = import_p_definitions.bind(py);
        for j in 0..import_p_defs_b.len() {
            let d_any = import_p_defs_b.get_item(j)?;
            let d_typed: Py<Definition> = d_any.downcast::<Definition>()?.clone().unbind();
            let d_borrow = d_typed.borrow(py);
            let bare = bare_name(&module_name, &d_borrow.name.borrow(py).name);
            let d_name_id = d_borrow.name.borrow(py).id;

            if is_native_import_def(py, &d_borrow)? {
                drop(d_borrow);
                prefixed_definitions.append(d_typed)?;
                continue;
            }

            let internal_name = Py::new(
                py,
                Name { name: format!("{}_{}", module_name, bare), id: d_name_id },
            )?;
            // Build a new Definition with the prefixed name.
            let prefixed_d = Py::new(
                py,
                (
                    Definition {
                        name: internal_name.clone_ref(py),
                        foralls: d_borrow.foralls.clone_ref(py),
                        args: d_borrow.args.clone_ref(py),
                        type_: d_borrow.type_.clone_ref(py),
                        body: d_borrow.body.clone_ref(py),
                        decorators: d_borrow.decorators.clone_ref(py),
                        rforalls: d_borrow.rforalls.clone_ref(py),
                        decreasing_by: d_borrow.decreasing_by.clone_ref(py),
                        arg_multiplicities: d_borrow.arg_multiplicities.clone_ref(py),
                        loc: d_borrow.loc.clone_ref(py),
                    },
                    crate::sugar::Node,
                ),
            )?;
            drop(d_borrow);
            prefixed_definitions.append(prefixed_d)?;

            qualified_scope.insert(
                (module_name.clone(), bare.clone()),
                internal_name.clone_ref(py),
            );

            if is_open {
                unqualified_scope.insert(bare.clone(), internal_name.clone_ref(py));
            } else if !selected_names.is_empty() && selected_names.contains(&bare) {
                unqualified_scope.insert(bare.clone(), internal_name.clone_ref(py));
            }
        }

        // defs = defs_recursive ++ prefixed_definitions ++ defs
        let new_defs = PyList::empty_bound(py);
        copy_list_into(py, &new_defs, &defs_recursive)?;
        for k in 0..prefixed_definitions.len() {
            new_defs.append(prefixed_definitions.get_item(k)?)?;
        }
        copy_list_into(py, &new_defs, &defs)?;
        defs = new_defs.unbind();

        // type_decls = type_decls_recursive ++ import_p.type_decls ++ type_decls
        let new_td = PyList::empty_bound(py);
        copy_list_into(py, &new_td, &type_decls_recursive)?;
        copy_list_into(py, &new_td, &import_p_type_decls)?;
        copy_list_into(py, &new_td, &type_decls)?;
        type_decls = new_td.unbind();
    }

    Ok((defs, type_decls, qualified_scope, unqualified_scope))
}

fn qscope_to_pydict(py: Python<'_>, q: &QualifiedScope) -> PyResult<Py<PyDict>> {
    let d = PyDict::new_bound(py);
    for ((m, b), v) in q {
        let key = (m.as_str(), b.as_str());
        let tup = pyo3::types::PyTuple::new_bound(py, [key.0, key.1]);
        d.set_item(tup, v.clone_ref(py))?;
    }
    Ok(d.unbind())
}

fn uscope_to_pydict(py: Python<'_>, u: &UnqualifiedScope) -> PyResult<Py<PyDict>> {
    let d = PyDict::new_bound(py);
    for (k, v) in u {
        d.set_item(k, v.clone_ref(py))?;
    }
    Ok(d.unbind())
}

#[pyfunction]
pub fn py_handle_imports(
    py: Python<'_>,
    imports: Py<PyList>,
    defs: Py<PyList>,
    type_decls: Py<PyList>,
) -> PyResult<(Py<PyList>, Py<PyList>, Py<PyDict>, Py<PyDict>)> {
    let (d, td, q, u) = handle_imports(py, imports, defs, type_decls)?;
    Ok((d, td, qscope_to_pydict(py, &q)?, uscope_to_pydict(py, &u)?))
}

// ---- apply_decorators_in_definitions / _in_program ----------------------

/// Call `aeon.decorators.apply_decorators(definition, metadata)` and unpack
/// the returned `(new_def, other_defs, metadata)` tuple.
fn call_apply_decorators(
    py: Python<'_>,
    definition: &Py<Definition>,
    metadata: &Py<PyDict>,
) -> PyResult<(Py<Definition>, Py<PyList>, Py<PyDict>)> {
    let module = py.import_bound("aeon.decorators")?;
    let f = module.getattr("apply_decorators")?;
    let res = f.call1((definition.clone_ref(py), metadata.clone_ref(py)))?;
    let new_def: Py<Definition> = res.get_item(0)?.downcast::<Definition>()?.clone().unbind();
    let other_defs: Py<PyList> = res.get_item(1)?.downcast::<PyList>()?.clone().unbind();
    let new_metadata: Py<PyDict> = res.get_item(2)?.downcast::<PyDict>()?.clone().unbind();
    Ok((new_def, other_defs, new_metadata))
}

#[pyfunction]
pub fn apply_decorators_in_definitions(
    py: Python<'_>,
    definitions: Py<PyList>,
) -> PyResult<(Py<PyList>, Py<PyDict>)> {
    let mut metadata: Py<PyDict> = PyDict::new_bound(py).unbind();
    let new_definitions = PyList::empty_bound(py);
    let defs_b = definitions.bind(py);
    for i in 0..defs_b.len() {
        let d: Py<Definition> = defs_b.get_item(i)?.downcast::<Definition>()?.clone().unbind();
        let (new_def, other_defs, new_md) = call_apply_decorators(py, &d, &metadata)?;
        metadata = new_md;
        new_definitions.append(new_def)?;
        let other_b = other_defs.bind(py);
        for j in 0..other_b.len() {
            new_definitions.append(other_b.get_item(j)?)?;
        }
    }
    Ok((new_definitions.unbind(), metadata))
}

#[pyfunction]
pub fn apply_decorators_in_program(py: Python<'_>, prog: Py<Program>) -> PyResult<Py<Program>> {
    let pb = prog.borrow(py);
    let imports = pb.imports.clone_ref(py);
    let type_decls = pb.type_decls.clone_ref(py);
    let inductive_decls = pb.inductive_decls.clone_ref(py);
    let definitions = pb.definitions.clone_ref(py);
    drop(pb);
    let (new_defs, _md) = apply_decorators_in_definitions(py, definitions)?;
    Py::new(
        py,
        (
            Program {
                imports,
                type_decls,
                inductive_decls,
                definitions: new_defs,
            },
            crate::sugar::Node,
        ),
    )
}

/// Wraps `aeon.decorators.collect_core_decorator_queue(defs, metadata)`.
fn call_collect_core_decorator_queue(
    py: Python<'_>,
    defs: Py<PyList>,
    metadata: Py<PyDict>,
) -> PyResult<(Py<PyList>, Py<PyDict>)> {
    let module = py.import_bound("aeon.decorators")?;
    let f = module.getattr("collect_core_decorator_queue")?;
    let res = f.call1((defs, metadata))?;
    let new_defs: Py<PyList> = res.get_item(0)?.downcast::<PyList>()?.clone().unbind();
    let new_md: Py<PyDict> = res.get_item(1)?.downcast::<PyDict>()?.clone().unbind();
    Ok((new_defs, new_md))
}

// ---- desugar driver -----------------------------------------------------

/// `aeon.prelude.prelude.typing_vars` — fetched via FFI.
fn typing_vars(py: Python<'_>) -> PyResult<Py<PyDict>> {
    let m = py.import_bound("aeon.prelude.prelude")?;
    let v = m.getattr("typing_vars")?;
    Ok(v.downcast::<PyDict>()?.clone().unbind())
}

#[pyfunction]
#[pyo3(signature = (p, is_main_hole = None, extra_vars = None))]
pub fn desugar(
    py: Python<'_>,
    p: Py<Program>,
    is_main_hole: Option<PyObject>,
    extra_vars: Option<Py<PyDict>>,
) -> PyResult<Py<DesugaredProgram>> {
    // vs = (extra_vars or {}) ∪ typing_vars
    let vs = PyDict::new_bound(py);
    if let Some(ev) = extra_vars.as_ref() {
        for (k, v) in ev.bind(py).iter() {
            vs.set_item(k, v)?;
        }
    }
    let tv = typing_vars(py)?;
    for (k, v) in tv.bind(py).iter() {
        vs.set_item(k, v)?;
    }
    let vs: Py<PyDict> = vs.unbind();

    // is_main_hole: truthy?
    let is_main_hole_b: bool = match is_main_hole {
        Some(o) => o.bind(py).is_truthy()?,
        None => true,
    };

    // Step 1: infer inductive rforall decls.
    let p1 = infer_inductive_rforall_decls(py, p)?;

    // Snapshot inductive_decls before expansion (which clears them).
    let inductive_decls_snapshot: Py<PyList> = {
        let p1b = p1.borrow(py);
        let snap = PyList::empty_bound(py);
        let ids = p1b.inductive_decls.bind(py);
        for i in 0..ids.len() {
            snap.append(ids.get_item(i)?)?;
        }
        snap.unbind()
    };

    // Step 2: expand inductive decls.
    let p2 = expand_inductive_decls(py, p1)?;

    // Step 3: determine main function.
    let is_main_hole_py: PyObject = is_main_hole_b.into_py(py);
    let prog = determine_main_function(py, p2.clone_ref(py), Some(is_main_hole_py))?;

    let p2b = p2.borrow(py);
    let mut defs = p2b.definitions.clone_ref(py);
    let mut type_decls = p2b.type_decls.clone_ref(py);
    let p_imports = p2b.imports.clone_ref(py);
    drop(p2b);

    // Step 4: separate "open InductiveType" from file imports.
    let mut inductive_names: HashSet<String> = HashSet::new();
    {
        let snap_b = inductive_decls_snapshot.bind(py);
        for i in 0..snap_b.len() {
            let decl = snap_b.get_item(i)?;
            let name = decl.getattr("name")?;
            let n: Py<Name> = name.downcast::<Name>()?.clone().unbind();
            inductive_names.insert(n.borrow(py).name.clone());
        }
    }
    let file_imports = PyList::empty_bound(py);
    let mut open_inductives: HashSet<String> = HashSet::new();
    {
        let imps_b = p_imports.bind(py);
        for i in 0..imps_b.len() {
            let imp_any = imps_b.get_item(i)?;
            let imp: Py<ImportAe> = imp_any.downcast::<ImportAe>()?.clone().unbind();
            let imp_b = imp.borrow(py);
            let is_open = imp_b.is_open;
            let module_path = imp_b.module_path.clone();
            drop(imp_b);
            if is_open && inductive_names.contains(&module_path) {
                open_inductives.insert(module_path);
            } else {
                file_imports.append(imp)?;
            }
        }
    }

    // Step 5: handle file imports.
    let (new_defs, new_type_decls, mut qualified_scope, mut unqualified_scope) =
        handle_imports(py, file_imports.unbind(), defs, type_decls)?;
    defs = new_defs;
    type_decls = new_type_decls;

    // Step 6: register inductive constructors.
    let constructor_to_type = PyDict::new_bound(py);
    let constructor_defs = PyDict::new_bound(py);
    {
        let snap_b = inductive_decls_snapshot.bind(py);
        for i in 0..snap_b.len() {
            let decl = snap_b.get_item(i)?;
            let decl_name_any = decl.getattr("name")?;
            let decl_name: Py<Name> = decl_name_any.downcast::<Name>()?.clone().unbind();
            let decl_name_str = decl_name.borrow(py).name.clone();
            let constructors = decl.getattr("constructors")?;
            let cons_list = constructors.downcast::<PyList>()?;
            for j in 0..cons_list.len() {
                let cons = cons_list.get_item(j)?;
                let cons_name_any = cons.getattr("name")?;
                let cons_name: Py<Name> = cons_name_any.downcast::<Name>()?.clone().unbind();
                let cons_name_str = cons_name.borrow(py).name.clone();
                let cons_name_id = cons_name.borrow(py).id;
                let prefixed = Py::new(
                    py,
                    Name {
                        name: format!("{}_{}", decl_name_str, cons_name_str),
                        id: cons_name_id,
                    },
                )?;
                qualified_scope.insert(
                    (decl_name_str.clone(), cons_name_str.clone()),
                    prefixed.clone_ref(py),
                );
                constructor_to_type.set_item(&cons_name_str, decl_name.clone_ref(py))?;
                constructor_defs.set_item(&cons_name_str, prefixed.clone_ref(py))?;
                if open_inductives.contains(&decl_name_str) {
                    unqualified_scope.insert(cons_name_str.clone(), prefixed.clone_ref(py));
                }
            }
        }
    }

    let q_dict = qscope_to_pydict(py, &qualified_scope)?;
    let u_dict = uscope_to_pydict(py, &unqualified_scope)?;

    // Step 7: resolve qualified names in definitions and main program term.
    let new_defs = PyList::empty_bound(py);
    {
        let defs_b = defs.bind(py);
        for i in 0..defs_b.len() {
            let d: Py<Definition> = defs_b.get_item(i)?.downcast::<Definition>()?.clone().unbind();
            let nd = resolve_qualified_names_in_definition(
                py,
                d,
                q_dict.clone_ref(py),
                u_dict.clone_ref(py),
                Some(constructor_defs.clone().unbind()),
            )?;
            new_defs.append(nd)?;
        }
    }
    defs = new_defs.unbind();

    let prog = resolve_qualified_names_in_sterm(
        py,
        prog,
        q_dict.clone_ref(py),
        u_dict.clone_ref(py),
        Some(constructor_defs.clone().unbind()),
    )?;

    // Step 8: apply decorators (in-definitions) and collect tactic scripts.
    let (defs2, metadata) = apply_decorators_in_definitions(py, defs)?;
    let (defs3, metadata) = lower_by_blocks_in_definitions(py, defs2, metadata)?;

    // Step 9: introduce forall/rforall in types.
    let defs4 = introduce_forall_in_types(py, defs3, type_decls.clone_ref(py))?;
    let defs5 = introduce_rforall_in_types(py, defs4)?;

    // Step 10: core decorator queue.
    let (defs6, metadata) = call_collect_core_decorator_queue(py, defs5, metadata)?;

    // Step 11: build elaboration typing context.
    let etctx_struct = build_typing_context(
        py,
        vs.clone_ref(py),
        Some(type_decls.clone_ref(py)),
        Some(constructor_to_type.clone().unbind()),
        Some(constructor_defs.clone().unbind()),
    )?;
    let etctx: Py<ElaborationTypingContext> = Py::new(py, etctx_struct)?;

    // Step 12: update program & context.
    let (etctx, prog) = update_program_and_context(py, prog, defs6, etctx)?;

    // Step 13: replace_concrete_types — builtin_types + declared type names.
    let names_list = PyList::empty_bound(py);
    for t in [
        "Top", "Bool", "Int", "Float", "String", "Unit", "Set", "Tensor", "GpuConfig",
    ] {
        let n = Py::new(py, Name { name: t.to_string(), id: 0 })?;
        names_list.append(n)?;
    }
    {
        let td_b = type_decls.bind(py);
        for i in 0..td_b.len() {
            let td_any = td_b.get_item(i)?;
            let td: Py<TypeDecl> = td_any.downcast::<TypeDecl>()?.clone().unbind();
            let n = td.borrow(py).name.clone_ref(py);
            names_list.append(n)?;
        }
    }
    let (prog, etctx) = replace_concrete_types(py, prog, etctx, names_list.unbind())?;

    // Step 14: lower match.
    let prog = lower_match_to_inductive_rec(py, prog, inductive_decls_snapshot)?;

    // Build the result.
    Py::new(
        py,
        DesugaredProgram {
            program: prog,
            elabcontext: etctx,
            metadata: metadata.into_any(),
            constructor_to_type: constructor_to_type.unbind(),
            constructor_defs: constructor_defs.unbind(),
        },
    )
}

// Silence unused-import warnings for items only used indirectly.
#[allow(dead_code)]
fn _force_use(
    _stm: STerm,
    _td: TypeDecl,
    _def: Definition,
    _ctx: ElaborationTypingContext,
    _conv: fn(Python<'_>, Py<crate::sugar::STerm>, Py<Definition>) -> PyResult<PyObject>,
) {
    let _ = convert_definition_to_srec;
    let _ = definition_with_inferred_decreasing;
    let _ = resolve_qualified_names_in_stype;
    let _ = type_of_definition;
}
