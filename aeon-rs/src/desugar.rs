//! Algorithmic core of `aeon.sugar.desugar`.
//!
//! The pure-AST transforms live here; the imperative orchestration glue
//! (file-I/O `handle_imports`, `desugar` top-level driver, decorator pass)
//! stays in Python because it depends on lark-based parsing, the Python
//! decorator system, and other deeply Python-coupled pieces.

use std::collections::HashSet;

use pyo3::create_exception;
use pyo3::exceptions::{PyAssertionError, PyNameError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyString, PyTuple};

use crate::elabctx::{
    ElabTypingContextEntry, ElabUninterpretedBinder, ElabVariableBinder,
    ElaborationTypingContext,
};
use crate::kind::BaseKind;
use crate::name::{next_fresh_id, Name};
use crate::sugar::{
    Decorator, Definition, InductiveDecl, Node, Program, SAbstraction, SAbstractionType,
    SAnnotation, SAnonConstructor, SApplication, SBy, SHole, SIf, SLet, SLiteral, SMatch,
    SMatchBranch, SQualifiedVar, SRec, SRefinedType, SRefinementAbstraction,
    SRefinementApplication, SRefinementPolymorphism, STerm, STypeAbstraction, STypeApplication,
    STypeConstructor, STypePolymorphism, STypeVar, SType, SVar, TypeDecl,
};
use crate::sugar_helpers::{substitute_svartype_in_stype, substitution_svartype_in_sterm, type_equality};
use crate::kind::Kind;

create_exception!(aeon_rs, DesugarError, pyo3::exceptions::PyException);

// =============================================================================
// Helpers
// =============================================================================

fn pyname_eq(py: Python<'_>, a: &Py<Name>, b: &Py<Name>) -> bool {
    let a = a.borrow(py);
    let b = b.borrow(py);
    a.name == b.name && a.id == b.id
}

fn name_str(py: Python<'_>, n: &Py<Name>) -> String {
    n.borrow(py).name.clone()
}

fn name_id(py: Python<'_>, n: &Py<Name>) -> i64 {
    n.borrow(py).id
}

fn mk_name(py: Python<'_>, name: &str, id: i64) -> PyResult<Py<Name>> {
    Py::new(py, Name { name: name.to_string(), id })
}

fn default_loc(py: Python<'_>) -> PyObject {
    crate::loc::default_location(py)
}

// Build SVar wrapped Py.
fn mk_svar(py: Python<'_>, name: Py<Name>, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (SVar { name, loc }, STerm))?.into_any())
}

fn mk_shole(py: Python<'_>, name: Py<Name>, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (SHole { name, loc }, STerm))?.into_any())
}

fn mk_sannotation(py: Python<'_>, expr: PyObject, ty: PyObject, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (SAnnotation { expr, type_: ty, loc }, STerm))?.into_any())
}

fn mk_sapplication(py: Python<'_>, fun: PyObject, arg: PyObject, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (SApplication { fun, arg, loc }, STerm))?.into_any())
}

fn mk_sabstraction(py: Python<'_>, var_name: Py<Name>, body: PyObject, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (SAbstraction { var_name, body, loc }, STerm))?.into_any())
}

fn mk_stypeapplication(py: Python<'_>, body: PyObject, ty: PyObject, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (STypeApplication { body, type_: ty, loc }, STerm))?.into_any())
}

fn mk_srefinement_application(
    py: Python<'_>,
    body: PyObject,
    refinement: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (SRefinementApplication { body, refinement, loc }, STerm))?.into_any())
}

fn mk_stypeabstraction(
    py: Python<'_>,
    name: Py<Name>,
    kind: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (STypeAbstraction { name, kind, body, loc }, STerm))?.into_any())
}

fn mk_srefinement_abstraction(
    py: Python<'_>,
    name: Py<Name>,
    sort: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (SRefinementAbstraction { name, sort, body, loc }, STerm))?.into_any())
}

fn mk_sif(
    py: Python<'_>,
    cond: PyObject,
    then: PyObject,
    otherwise: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (SIf { cond, then, otherwise, loc }, STerm))?.into_any())
}

fn mk_smatch(
    py: Python<'_>,
    scrutinee: PyObject,
    branches: Py<PyList>,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (SMatch { scrutinee, branches, loc }, STerm))?.into_any())
}

fn mk_slet(
    py: Python<'_>,
    var_name: Py<Name>,
    var_value: PyObject,
    body: PyObject,
    loc: PyObject,
    multiplicity: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (SLet { var_name, var_value, body, loc, multiplicity }, STerm))?.into_any())
}

#[allow(clippy::too_many_arguments)]
fn mk_srec(
    py: Python<'_>,
    var_name: Py<Name>,
    var_type: PyObject,
    var_value: PyObject,
    body: PyObject,
    decreasing_by: Py<PyTuple>,
    loc: PyObject,
    multiplicity: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(
        py,
        (
            SRec { var_name, var_type, var_value, body, decreasing_by, loc, multiplicity },
            STerm,
        ),
    )?
    .into_any())
}

fn mk_srefinedtype(
    py: Python<'_>,
    name: Py<Name>,
    ty: PyObject,
    refinement: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (SRefinedType { name, type_: ty, refinement, loc }, SType))?.into_any())
}

fn mk_sabstractiontype(
    py: Python<'_>,
    var_name: Py<Name>,
    var_type: PyObject,
    return_type: PyObject,
    loc: PyObject,
    multiplicity: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(
        py,
        (
            SAbstractionType { var_name, var_type, type_: return_type, loc, multiplicity },
            SType,
        ),
    )?
    .into_any())
}

fn mk_stypepolymorphism(
    py: Python<'_>,
    name: Py<Name>,
    kind: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (STypePolymorphism { name, kind, body, loc }, SType))?.into_any())
}

fn mk_srefinement_polymorphism(
    py: Python<'_>,
    name: Py<Name>,
    sort: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (SRefinementPolymorphism { name, sort, body, loc }, SType))?.into_any())
}

fn mk_stypeconstructor(
    py: Python<'_>,
    name: Py<Name>,
    args: Py<PyList>,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (STypeConstructor { name, args, loc }, SType))?.into_any())
}

fn mk_stypevar(py: Python<'_>, name: Py<Name>, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (STypeVar { name, loc }, SType))?.into_any())
}

// Built-in sugar literal types (`st_int`, `st_string`) — instantiated fresh.
fn st_int(py: Python<'_>) -> PyResult<PyObject> {
    let n = mk_name(py, "Int", 0)?;
    mk_stypeconstructor(py, n, PyList::empty_bound(py).unbind(), default_loc(py))
}

fn st_string(py: Python<'_>) -> PyResult<PyObject> {
    let n = mk_name(py, "String", 0)?;
    mk_stypeconstructor(py, n, PyList::empty_bound(py).unbind(), default_loc(py))
}

// =============================================================================
// _stype_base_int
// =============================================================================

fn stype_base_int(py: Python<'_>, ty: &PyObject) -> bool {
    let b = ty.bind(py);
    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let rt = rt.borrow();
        let inner = rt.type_.clone_ref(py);
        return stype_base_int(py, &inner);
    }
    if let Ok(tc) = b.downcast::<STypeConstructor>() {
        let tc = tc.borrow();
        let n = tc.name.borrow(py);
        return n.name == "Int";
    }
    false
}

// =============================================================================
// _sugar_contains_recursive_call
// =============================================================================

fn is_call_tree(py: Python<'_>, node: &PyObject, fname: &Py<Name>) -> bool {
    let mut cur = node.clone_ref(py);
    loop {
        let b = cur.bind(py);
        if let Ok(app) = b.downcast::<SApplication>() {
            let inner = app.borrow().fun.clone_ref(py);
            drop(b);
            cur = inner;
        } else {
            break;
        }
    }
    let b = cur.bind(py);
    if let Ok(sv) = b.downcast::<SVar>() {
        let sv = sv.borrow();
        return pyname_eq(py, &sv.name, fname);
    }
    false
}

fn sugar_contains_recursive_call(py: Python<'_>, t: &PyObject, fname: &Py<Name>) -> PyResult<bool> {
    let b = t.bind(py);
    if let Ok(app) = b.downcast::<SApplication>() {
        if is_call_tree(py, t, fname) {
            return Ok(true);
        }
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        drop(app);
        return Ok(sugar_contains_recursive_call(py, &fun, fname)?
            || sugar_contains_recursive_call(py, &arg, fname)?);
    }
    if let Ok(ab) = b.downcast::<SAbstraction>() {
        let body = ab.borrow().body.clone_ref(py);
        return sugar_contains_recursive_call(py, &body, fname);
    }
    if let Ok(sl) = b.downcast::<SLet>() {
        let sl = sl.borrow();
        let v = sl.var_value.clone_ref(py);
        let bo = sl.body.clone_ref(py);
        drop(sl);
        return Ok(sugar_contains_recursive_call(py, &v, fname)?
            || sugar_contains_recursive_call(py, &bo, fname)?);
    }
    if let Ok(sr) = b.downcast::<SRec>() {
        let sr = sr.borrow();
        let v = sr.var_value.clone_ref(py);
        let bo = sr.body.clone_ref(py);
        drop(sr);
        return Ok(sugar_contains_recursive_call(py, &v, fname)?
            || sugar_contains_recursive_call(py, &bo, fname)?);
    }
    if let Ok(si) = b.downcast::<SIf>() {
        let si = si.borrow();
        let c = si.cond.clone_ref(py);
        let t1 = si.then.clone_ref(py);
        let e = si.otherwise.clone_ref(py);
        drop(si);
        return Ok(sugar_contains_recursive_call(py, &c, fname)?
            || sugar_contains_recursive_call(py, &t1, fname)?
            || sugar_contains_recursive_call(py, &e, fname)?);
    }
    if let Ok(sa) = b.downcast::<SAnnotation>() {
        let e = sa.borrow().expr.clone_ref(py);
        return sugar_contains_recursive_call(py, &e, fname);
    }
    if let Ok(sm) = b.downcast::<SMatch>() {
        let sm = sm.borrow();
        let scrut = sm.scrutinee.clone_ref(py);
        if sugar_contains_recursive_call(py, &scrut, fname)? {
            return Ok(true);
        }
        let branches = sm.branches.clone_ref(py);
        drop(sm);
        let bl = branches.bind(py);
        for i in 0..bl.len() {
            let br = bl.get_item(i)?;
            let br = br.downcast::<SMatchBranch>()?;
            let body = br.borrow().body.clone_ref(py);
            if sugar_contains_recursive_call(py, &body, fname)? {
                return Ok(true);
            }
        }
        return Ok(false);
    }
    Ok(false)
}

// =============================================================================
// definition_with_inferred_decreasing
// =============================================================================

#[pyfunction]
pub fn definition_with_inferred_decreasing(
    py: Python<'_>,
    d: Py<Definition>,
) -> PyResult<Py<Definition>> {
    let db = d.borrow(py);
    let decr = db.decreasing_by.bind(py);
    let args = db.args.bind(py);
    if decr.len() > 0 || args.len() != 1 {
        drop(db);
        return Ok(d);
    }
    let pair = args.get_item(0)?;
    let pname: Py<Name> = pair.get_item(0)?.downcast::<Name>()?.clone().unbind();
    let pty: PyObject = pair.get_item(1)?.unbind();
    if !stype_base_int(py, &pty) {
        drop(db);
        return Ok(d);
    }
    let body = db.body.clone_ref(py);
    let name = db.name.clone_ref(py);
    if !sugar_contains_recursive_call(py, &body, &name)? {
        drop(db);
        return Ok(d);
    }

    // Construct decreasing_by = [SVar(pname)]
    let sv = mk_svar(py, pname.clone_ref(py), default_loc(py))?;
    let new_decr = PyList::empty_bound(py);
    new_decr.append(sv)?;

    let new_def = Py::new(
        py,
        (
            Definition {
                name,
                foralls: db.foralls.clone_ref(py),
                args: db.args.clone_ref(py),
                type_: db.type_.clone_ref(py),
                body: db.body.clone_ref(py),
                decorators: db.decorators.clone_ref(py),
                rforalls: db.rforalls.clone_ref(py),
                decreasing_by: new_decr.unbind(),
                arg_multiplicities: db.arg_multiplicities.clone_ref(py),
                loc: db.loc.clone_ref(py),
            },
            Node,
        ),
    )?;
    Ok(new_def)
}

// =============================================================================
// DesugaredProgram
// =============================================================================

#[pyclass(module = "aeon_rs", frozen)]
pub struct DesugaredProgram {
    #[pyo3(get)]
    pub program: PyObject,
    #[pyo3(get)]
    pub elabcontext: Py<ElaborationTypingContext>,
    #[pyo3(get)]
    pub metadata: PyObject,
    #[pyo3(get)]
    pub constructor_to_type: Py<PyDict>,
    #[pyo3(get)]
    pub constructor_defs: Py<PyDict>,
}

#[pymethods]
impl DesugaredProgram {
    #[new]
    #[pyo3(signature = (program, elabcontext, metadata, constructor_to_type = None, constructor_defs = None))]
    fn py_new(
        py: Python<'_>,
        program: PyObject,
        elabcontext: Py<ElaborationTypingContext>,
        metadata: PyObject,
        constructor_to_type: Option<Py<PyDict>>,
        constructor_defs: Option<Py<PyDict>>,
    ) -> Self {
        DesugaredProgram {
            program,
            elabcontext,
            metadata,
            constructor_to_type: constructor_to_type.unwrap_or_else(|| PyDict::new_bound(py).unbind()),
            constructor_defs: constructor_defs.unwrap_or_else(|| PyDict::new_bound(py).unbind()),
        }
    }

    #[classattr]
    fn __match_args__<'py>(py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::new_bound(
            py,
            &["program", "elabcontext", "metadata", "constructor_to_type", "constructor_defs"],
        )
    }

    fn __iter__(slf: PyRef<'_, Self>, py: Python<'_>) -> PyResult<PyObject> {
        let lst = PyList::empty_bound(py);
        lst.append(slf.program.clone_ref(py))?;
        lst.append(slf.elabcontext.clone_ref(py))?;
        lst.append(slf.metadata.clone_ref(py))?;
        lst.append(slf.constructor_to_type.clone_ref(py))?;
        lst.append(slf.constructor_defs.clone_ref(py))?;
        let it = lst.as_any().call_method0("__iter__")?;
        Ok(it.unbind())
    }

    fn __getitem__(&self, py: Python<'_>, idx: isize) -> PyResult<PyObject> {
        let i = if idx < 0 { idx + 5 } else { idx };
        match i {
            0 => Ok(self.program.clone_ref(py)),
            1 => Ok(self.elabcontext.clone_ref(py).into_any()),
            2 => Ok(self.metadata.clone_ref(py)),
            3 => Ok(self.constructor_to_type.clone_ref(py).into_any()),
            4 => Ok(self.constructor_defs.clone_ref(py).into_any()),
            _ => Err(PyAssertionError::new_err("index out of range")),
        }
    }

    fn __len__(&self) -> usize {
        5
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "DesugaredProgram(program={}, elabcontext=..., metadata=..., constructor_to_type=..., constructor_defs=...)",
            self.program.bind(py).str()?
        ))
    }
}

// =============================================================================
// lower_by_blocks_in_sterm
// =============================================================================

fn merge_scripts(py: Python<'_>, a: &Bound<'_, PyDict>, b: &Bound<'_, PyDict>) -> PyResult<()> {
    // Mutate `a` to merge entries from `b`, raising on conflict.
    for (k, v) in b.iter() {
        if let Some(existing) = a.get_item(&k)? {
            // both must be equal — compare via tuple equality
            if !existing.eq(&v)? {
                return Err(PyValueError::new_err(format!(
                    "Conflicting tactic scripts for hole {}",
                    k.str()?
                )));
            }
        }
        a.set_item(k, v)?;
    }
    Ok(())
}

fn lower_by_blocks_in_sterm_inner(
    py: Python<'_>,
    t: PyObject,
) -> PyResult<(PyObject, Py<PyDict>)> {
    let b = t.bind(py);

    // SBy: replace with fresh SHole and record tactic script
    if let Ok(by) = b.downcast::<SBy>() {
        let by = by.borrow();
        let steps = by.steps.clone_ref(py);
        let loc = by.loc.clone_ref(py);
        drop(by);
        let new_id = next_fresh_id(py)?;
        let h_name = mk_name(py, "_by", new_id)?;
        let hole = mk_shole(py, h_name.clone_ref(py), loc)?;
        let d = PyDict::new_bound(py);
        d.set_item(h_name, steps)?;
        return Ok((hole, d.unbind()));
    }

    // Leaves: SLiteral, SVar, SHole, SQualifiedVar, SAnonConstructor
    if b.downcast::<SLiteral>().is_ok()
        || b.downcast::<SVar>().is_ok()
        || b.downcast::<SHole>().is_ok()
        || b.downcast::<SQualifiedVar>().is_ok()
        || b.downcast::<SAnonConstructor>().is_ok()
    {
        return Ok((t, PyDict::new_bound(py).unbind()));
    }

    if let Ok(sa) = b.downcast::<SAnnotation>() {
        let sa = sa.borrow();
        let expr = sa.expr.clone_ref(py);
        let ty = sa.type_.clone_ref(py);
        let loc = sa.loc.clone_ref(py);
        drop(sa);
        let (ne, s1) = lower_by_blocks_in_sterm_inner(py, expr)?;
        let out = mk_sannotation(py, ne, ty, loc)?;
        return Ok((out, s1));
    }

    if let Ok(sapp) = b.downcast::<SApplication>() {
        let sapp = sapp.borrow();
        let fun = sapp.fun.clone_ref(py);
        let arg = sapp.arg.clone_ref(py);
        let loc = sapp.loc.clone_ref(py);
        drop(sapp);
        let (nf, s1) = lower_by_blocks_in_sterm_inner(py, fun)?;
        let (na, s2) = lower_by_blocks_in_sterm_inner(py, arg)?;
        let s1b = s1.bind(py).clone();
        let s2b = s2.bind(py);
        merge_scripts(py, &s1b, s2b)?;
        let out = mk_sapplication(py, nf, na, loc)?;
        return Ok((out, s1));
    }

    if let Ok(sab) = b.downcast::<SAbstraction>() {
        let sab = sab.borrow();
        let name = sab.var_name.clone_ref(py);
        let body = sab.body.clone_ref(py);
        let loc = sab.loc.clone_ref(py);
        drop(sab);
        let (nb, s1) = lower_by_blocks_in_sterm_inner(py, body)?;
        let out = mk_sabstraction(py, name, nb, loc)?;
        return Ok((out, s1));
    }

    if let Ok(sta) = b.downcast::<STypeApplication>() {
        let sta = sta.borrow();
        let body = sta.body.clone_ref(py);
        let ty = sta.type_.clone_ref(py);
        let loc = sta.loc.clone_ref(py);
        drop(sta);
        let (nb, s1) = lower_by_blocks_in_sterm_inner(py, body)?;
        let out = mk_stypeapplication(py, nb, ty, loc)?;
        return Ok((out, s1));
    }

    if let Ok(sra) = b.downcast::<SRefinementApplication>() {
        let sra = sra.borrow();
        let body = sra.body.clone_ref(py);
        let refn = sra.refinement.clone_ref(py);
        let loc = sra.loc.clone_ref(py);
        drop(sra);
        let (nb, s1) = lower_by_blocks_in_sterm_inner(py, body)?;
        let (nr, s2) = lower_by_blocks_in_sterm_inner(py, refn)?;
        let s1b = s1.bind(py).clone();
        merge_scripts(py, &s1b, s2.bind(py))?;
        let out = mk_srefinement_application(py, nb, nr, loc)?;
        return Ok((out, s1));
    }

    if let Ok(sta) = b.downcast::<STypeAbstraction>() {
        let sta = sta.borrow();
        let name = sta.name.clone_ref(py);
        let kind = sta.kind.clone_ref(py);
        let body = sta.body.clone_ref(py);
        let loc = sta.loc.clone_ref(py);
        drop(sta);
        let (nb, s1) = lower_by_blocks_in_sterm_inner(py, body)?;
        let out = mk_stypeabstraction(py, name, kind, nb, loc)?;
        return Ok((out, s1));
    }

    if let Ok(sra) = b.downcast::<SRefinementAbstraction>() {
        let sra = sra.borrow();
        let name = sra.name.clone_ref(py);
        let sort = sra.sort.clone_ref(py);
        let body = sra.body.clone_ref(py);
        let loc = sra.loc.clone_ref(py);
        drop(sra);
        let (nb, s1) = lower_by_blocks_in_sterm_inner(py, body)?;
        let out = mk_srefinement_abstraction(py, name, sort, nb, loc)?;
        return Ok((out, s1));
    }

    if let Ok(sif) = b.downcast::<SIf>() {
        let sif = sif.borrow();
        let cond = sif.cond.clone_ref(py);
        let then = sif.then.clone_ref(py);
        let oth = sif.otherwise.clone_ref(py);
        let loc = sif.loc.clone_ref(py);
        drop(sif);
        let (nc, s1) = lower_by_blocks_in_sterm_inner(py, cond)?;
        let (nt, s2) = lower_by_blocks_in_sterm_inner(py, then)?;
        let (no, s3) = lower_by_blocks_in_sterm_inner(py, oth)?;
        let s1b = s1.bind(py).clone();
        merge_scripts(py, &s1b, s2.bind(py))?;
        merge_scripts(py, &s1b, s3.bind(py))?;
        let out = mk_sif(py, nc, nt, no, loc)?;
        return Ok((out, s1));
    }

    if let Ok(sm) = b.downcast::<SMatch>() {
        let sm = sm.borrow();
        let scrut = sm.scrutinee.clone_ref(py);
        let branches = sm.branches.clone_ref(py);
        let loc = sm.loc.clone_ref(py);
        drop(sm);
        let (ns, s0) = lower_by_blocks_in_sterm_inner(py, scrut)?;
        let new_branches = PyList::empty_bound(py);
        let acc = s0.bind(py).clone();
        let bs = branches.bind(py);
        for i in 0..bs.len() {
            let br = bs.get_item(i)?;
            let br = br.downcast::<SMatchBranch>()?;
            let br = br.borrow();
            let cons = br.constructor.clone_ref(py);
            let binders = br.binders.clone_ref(py);
            let body = br.body.clone_ref(py);
            let qual = br.qualifier.clone();
            let brloc = br.loc.clone_ref(py);
            drop(br);
            let (nb, sb) = lower_by_blocks_in_sterm_inner(py, body)?;
            merge_scripts(py, &acc, sb.bind(py))?;
            let new_br = Py::new(
                py,
                SMatchBranch { constructor: cons, binders, body: nb, qualifier: qual, loc: brloc },
            )?;
            new_branches.append(new_br)?;
        }
        let out = mk_smatch(py, ns, new_branches.unbind(), loc)?;
        return Ok((out, s0));
    }

    if let Ok(sl) = b.downcast::<SLet>() {
        let sl = sl.borrow();
        let name = sl.var_name.clone_ref(py);
        let v = sl.var_value.clone_ref(py);
        let bo = sl.body.clone_ref(py);
        let loc = sl.loc.clone_ref(py);
        let mult = sl.multiplicity.clone_ref(py);
        drop(sl);
        let (nv, s1) = lower_by_blocks_in_sterm_inner(py, v)?;
        let (nb, s2) = lower_by_blocks_in_sterm_inner(py, bo)?;
        let s1b = s1.bind(py).clone();
        merge_scripts(py, &s1b, s2.bind(py))?;
        let out = mk_slet(py, name, nv, nb, loc, mult)?;
        return Ok((out, s1));
    }

    if let Ok(sr) = b.downcast::<SRec>() {
        let sr = sr.borrow();
        let name = sr.var_name.clone_ref(py);
        let ty = sr.var_type.clone_ref(py);
        let v = sr.var_value.clone_ref(py);
        let bo = sr.body.clone_ref(py);
        let decr = sr.decreasing_by.clone_ref(py);
        let loc = sr.loc.clone_ref(py);
        let mult = sr.multiplicity.clone_ref(py);
        drop(sr);
        let (nv, s1) = lower_by_blocks_in_sterm_inner(py, v)?;
        let (nb, s2) = lower_by_blocks_in_sterm_inner(py, bo)?;
        let s1b = s1.bind(py).clone();
        merge_scripts(py, &s1b, s2.bind(py))?;
        let decr_b = decr.bind(py);
        let mut new_decr_vec: Vec<PyObject> = Vec::with_capacity(decr_b.len());
        for i in 0..decr_b.len() {
            let item = decr_b.get_item(i)?.unbind();
            let (ni, si) = lower_by_blocks_in_sterm_inner(py, item)?;
            merge_scripts(py, &s1b, si.bind(py))?;
            new_decr_vec.push(ni);
        }
        let new_decr_tuple = PyTuple::new_bound(py, new_decr_vec).unbind();
        let out = mk_srec(py, name, ty, nv, nb, new_decr_tuple, loc, mult)?;
        return Ok((out, s1));
    }

    Err(PyAssertionError::new_err(format!(
        "lower_by_blocks_in_sterm: unhandled {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

#[pyfunction]
pub fn lower_by_blocks_in_sterm(py: Python<'_>, t: PyObject) -> PyResult<(PyObject, Py<PyDict>)> {
    lower_by_blocks_in_sterm_inner(py, t)
}

// =============================================================================
// lower_by_blocks_in_definitions
// =============================================================================

#[pyfunction]
pub fn lower_by_blocks_in_definitions(
    py: Python<'_>,
    definitions: Py<PyList>,
    metadata: Py<PyDict>,
) -> PyResult<(Py<PyList>, Py<PyDict>)> {
    let out = PyList::empty_bound(py);
    let defs_b = definitions.bind(py);
    for i in 0..defs_b.len() {
        let dany = defs_b.get_item(i)?;
        let dpy = dany.downcast::<Definition>()?;
        let d = dpy.borrow();
        let body = d.body.clone_ref(py);
        let name = d.name.clone_ref(py);
        drop(d);

        let (nbody, scripts) = lower_by_blocks_in_sterm_inner(py, body)?;
        let scripts_b = scripts.bind(py);
        if scripts_b.len() > 0 {
            // Update metadata entry
            let md_b = metadata.bind(py);
            let cur: Bound<'_, PyDict> = match md_b.get_item(name.clone_ref(py))? {
                Some(existing) => {
                    // copy dict to avoid mutating caller's dict-of-dicts
                    let copy = PyDict::new_bound(py);
                    for (k, v) in existing.downcast::<PyDict>()?.iter() {
                        copy.set_item(k, v)?;
                    }
                    copy
                }
                None => PyDict::new_bound(py),
            };
            let ts: Bound<'_, PyDict> = match cur.get_item("tactic_scripts")? {
                Some(existing) => {
                    let copy = PyDict::new_bound(py);
                    for (k, v) in existing.downcast::<PyDict>()?.iter() {
                        copy.set_item(k, v)?;
                    }
                    copy
                }
                None => PyDict::new_bound(py),
            };
            for (h, steps) in scripts_b.iter() {
                if let Some(existing) = ts.get_item(&h)? {
                    if !existing.eq(&steps)? {
                        return Err(PyValueError::new_err(format!(
                            "Multiple conflicting `by` scripts for {} hole {}",
                            name.borrow(py).__str__(),
                            h.str()?
                        )));
                    }
                }
                ts.set_item(h, steps)?;
            }
            cur.set_item("tactic_scripts", ts)?;
            md_b.set_item(name.clone_ref(py), cur)?;
        }

        let dpy_b = dany.downcast::<Definition>()?.borrow();
        let new_def = Py::new(
            py,
            (
                Definition {
                    name: dpy_b.name.clone_ref(py),
                    foralls: dpy_b.foralls.clone_ref(py),
                    args: dpy_b.args.clone_ref(py),
                    type_: dpy_b.type_.clone_ref(py),
                    body: nbody,
                    decorators: dpy_b.decorators.clone_ref(py),
                    rforalls: dpy_b.rforalls.clone_ref(py),
                    decreasing_by: dpy_b.decreasing_by.clone_ref(py),
                    arg_multiplicities: dpy_b.arg_multiplicities.clone_ref(py),
                    loc: dpy_b.loc.clone_ref(py),
                },
                Node,
            ),
        )?;
        drop(dpy_b);
        out.append(new_def)?;
    }
    Ok((out.unbind(), metadata))
}

// =============================================================================
// resolve_qualified_names
// =============================================================================

fn resolve_qualified_names_in_sterm_inner(
    py: Python<'_>,
    t: PyObject,
    qualified_scope: &Bound<'_, PyDict>,
    unqualified_scope: &Bound<'_, PyDict>,
    constructor_defs: Option<&Bound<'_, PyDict>>,
) -> PyResult<PyObject> {
    let b = t.bind(py);

    if let Ok(ac) = b.downcast::<SAnonConstructor>() {
        let ac = ac.borrow();
        let cname = ac.name.clone();
        let loc = ac.loc.clone_ref(py);
        drop(ac);
        if let Some(cd) = constructor_defs {
            if let Some(val) = cd.get_item(&cname)? {
                let nname: Py<Name> = val.downcast::<Name>()?.clone().unbind();
                return mk_svar(py, nname, loc);
            }
        }
        return Ok(t);
    }

    if let Ok(qv) = b.downcast::<SQualifiedVar>() {
        let qv = qv.borrow();
        let qual = qv.qualifier.clone();
        let name_obj = qv.name.clone_ref(py);
        let loc = qv.loc.clone_ref(py);
        let nstr = name_str(py, &name_obj);
        drop(qv);
        let key = PyTuple::new_bound(py, &[qual.clone(), nstr.clone()]);
        if let Some(val) = qualified_scope.get_item(&key)? {
            let nname: Py<Name> = val.downcast::<Name>()?.clone().unbind();
            return mk_svar(py, nname, loc);
        }
        return Err(PyNameError::new_err(format!(
            "Name '{}' not found in module '{}'",
            nstr, qual
        )));
    }

    if let Ok(sv) = b.downcast::<SVar>() {
        let sv = sv.borrow();
        let name = sv.name.clone_ref(py);
        let loc = sv.loc.clone_ref(py);
        let nstr = name_str(py, &name);
        drop(sv);
        if let Some(val) = unqualified_scope.get_item(&nstr)? {
            let nname: Py<Name> = val.downcast::<Name>()?.clone().unbind();
            return mk_svar(py, nname, loc);
        }
        return Ok(t);
    }

    if let Ok(sapp) = b.downcast::<SApplication>() {
        let sapp = sapp.borrow();
        let fun = sapp.fun.clone_ref(py);
        let arg = sapp.arg.clone_ref(py);
        let loc = sapp.loc.clone_ref(py);
        drop(sapp);
        let nfun = resolve_qualified_names_in_sterm_inner(py, fun, qualified_scope, unqualified_scope, constructor_defs)?;
        let narg = resolve_qualified_names_in_sterm_inner(py, arg, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_sapplication(py, nfun, narg, loc);
    }

    if let Ok(ab) = b.downcast::<SAbstraction>() {
        let ab = ab.borrow();
        let name = ab.var_name.clone_ref(py);
        let body = ab.body.clone_ref(py);
        let loc = ab.loc.clone_ref(py);
        drop(ab);
        let nbody = resolve_qualified_names_in_sterm_inner(py, body, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_sabstraction(py, name, nbody, loc);
    }

    if let Ok(sl) = b.downcast::<SLet>() {
        let sl = sl.borrow();
        let name = sl.var_name.clone_ref(py);
        let v = sl.var_value.clone_ref(py);
        let bo = sl.body.clone_ref(py);
        let loc = sl.loc.clone_ref(py);
        let mult = sl.multiplicity.clone_ref(py);
        drop(sl);
        let nv = resolve_qualified_names_in_sterm_inner(py, v, qualified_scope, unqualified_scope, constructor_defs)?;
        let nb = resolve_qualified_names_in_sterm_inner(py, bo, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_slet(py, name, nv, nb, loc, mult);
    }

    if let Ok(sr) = b.downcast::<SRec>() {
        let sr = sr.borrow();
        let name = sr.var_name.clone_ref(py);
        let ty = sr.var_type.clone_ref(py);
        let v = sr.var_value.clone_ref(py);
        let bo = sr.body.clone_ref(py);
        let decr = sr.decreasing_by.clone_ref(py);
        let loc = sr.loc.clone_ref(py);
        let mult = sr.multiplicity.clone_ref(py);
        drop(sr);
        let nv = resolve_qualified_names_in_sterm_inner(py, v, qualified_scope, unqualified_scope, constructor_defs)?;
        let nb = resolve_qualified_names_in_sterm_inner(py, bo, qualified_scope, unqualified_scope, constructor_defs)?;
        let decr_b = decr.bind(py);
        let mut new_decr: Vec<PyObject> = Vec::with_capacity(decr_b.len());
        for i in 0..decr_b.len() {
            let m = decr_b.get_item(i)?.unbind();
            new_decr.push(resolve_qualified_names_in_sterm_inner(py, m, qualified_scope, unqualified_scope, constructor_defs)?);
        }
        let new_decr_tuple = PyTuple::new_bound(py, new_decr).unbind();
        return mk_srec(py, name, ty, nv, nb, new_decr_tuple, loc, mult);
    }

    if let Ok(si) = b.downcast::<SIf>() {
        let si = si.borrow();
        let cond = si.cond.clone_ref(py);
        let then = si.then.clone_ref(py);
        let oth = si.otherwise.clone_ref(py);
        let loc = si.loc.clone_ref(py);
        drop(si);
        let nc = resolve_qualified_names_in_sterm_inner(py, cond, qualified_scope, unqualified_scope, constructor_defs)?;
        let nt = resolve_qualified_names_in_sterm_inner(py, then, qualified_scope, unqualified_scope, constructor_defs)?;
        let no = resolve_qualified_names_in_sterm_inner(py, oth, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_sif(py, nc, nt, no, loc);
    }

    if let Ok(sa) = b.downcast::<SAnnotation>() {
        let sa = sa.borrow();
        let e = sa.expr.clone_ref(py);
        let ty = sa.type_.clone_ref(py);
        let loc = sa.loc.clone_ref(py);
        drop(sa);
        let ne = resolve_qualified_names_in_sterm_inner(py, e, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_sannotation(py, ne, ty, loc);
    }

    if let Ok(sta) = b.downcast::<STypeApplication>() {
        let sta = sta.borrow();
        let body = sta.body.clone_ref(py);
        let ty = sta.type_.clone_ref(py);
        let loc = sta.loc.clone_ref(py);
        drop(sta);
        let nb = resolve_qualified_names_in_sterm_inner(py, body, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_stypeapplication(py, nb, ty, loc);
    }

    if let Ok(sra) = b.downcast::<SRefinementApplication>() {
        let sra = sra.borrow();
        let body = sra.body.clone_ref(py);
        let refn = sra.refinement.clone_ref(py);
        let loc = sra.loc.clone_ref(py);
        drop(sra);
        let nb = resolve_qualified_names_in_sterm_inner(py, body, qualified_scope, unqualified_scope, constructor_defs)?;
        let nr = resolve_qualified_names_in_sterm_inner(py, refn, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_srefinement_application(py, nb, nr, loc);
    }

    if let Ok(sta) = b.downcast::<STypeAbstraction>() {
        let sta = sta.borrow();
        let name = sta.name.clone_ref(py);
        let kind = sta.kind.clone_ref(py);
        let body = sta.body.clone_ref(py);
        let loc = sta.loc.clone_ref(py);
        drop(sta);
        let nb = resolve_qualified_names_in_sterm_inner(py, body, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_stypeabstraction(py, name, kind, nb, loc);
    }

    if let Ok(sra) = b.downcast::<SRefinementAbstraction>() {
        let sra = sra.borrow();
        let name = sra.name.clone_ref(py);
        let sort = sra.sort.clone_ref(py);
        let body = sra.body.clone_ref(py);
        let loc = sra.loc.clone_ref(py);
        drop(sra);
        let nb = resolve_qualified_names_in_sterm_inner(py, body, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_srefinement_abstraction(py, name, sort, nb, loc);
    }

    if let Ok(sm) = b.downcast::<SMatch>() {
        let sm = sm.borrow();
        let scrut = sm.scrutinee.clone_ref(py);
        let branches = sm.branches.clone_ref(py);
        let loc = sm.loc.clone_ref(py);
        drop(sm);
        let nscrut = resolve_qualified_names_in_sterm_inner(py, scrut, qualified_scope, unqualified_scope, constructor_defs)?;
        let new_branches = PyList::empty_bound(py);
        let bs = branches.bind(py);
        for i in 0..bs.len() {
            let br = bs.get_item(i)?;
            let br = br.downcast::<SMatchBranch>()?;
            let br = br.borrow();
            let cons = br.constructor.clone_ref(py);
            let binders = br.binders.clone_ref(py);
            let body = br.body.clone_ref(py);
            let qual = br.qualifier.clone();
            let brloc = br.loc.clone_ref(py);
            drop(br);
            let nbody = resolve_qualified_names_in_sterm_inner(py, body, qualified_scope, unqualified_scope, constructor_defs)?;
            let new_br = Py::new(
                py,
                SMatchBranch { constructor: cons, binders, body: nbody, qualifier: qual, loc: brloc },
            )?;
            new_branches.append(new_br)?;
        }
        return mk_smatch(py, nscrut, new_branches.unbind(), loc);
    }

    Ok(t)
}

#[pyfunction]
#[pyo3(signature = (t, qualified_scope, unqualified_scope, constructor_defs = None))]
pub fn resolve_qualified_names_in_sterm(
    py: Python<'_>,
    t: PyObject,
    qualified_scope: Py<PyDict>,
    unqualified_scope: Py<PyDict>,
    constructor_defs: Option<Py<PyDict>>,
) -> PyResult<PyObject> {
    let qs = qualified_scope.bind(py).clone();
    let us = unqualified_scope.bind(py).clone();
    let cd = constructor_defs.as_ref().map(|d| d.bind(py).clone());
    resolve_qualified_names_in_sterm_inner(py, t, &qs, &us, cd.as_ref())
}

fn resolve_qualified_names_in_stype_inner(
    py: Python<'_>,
    ty: PyObject,
    qualified_scope: &Bound<'_, PyDict>,
    unqualified_scope: &Bound<'_, PyDict>,
    constructor_defs: Option<&Bound<'_, PyDict>>,
) -> PyResult<PyObject> {
    let b = ty.bind(py);

    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let rt = rt.borrow();
        let name = rt.name.clone_ref(py);
        let inner = rt.type_.clone_ref(py);
        let refn = rt.refinement.clone_ref(py);
        let loc = rt.loc.clone_ref(py);
        drop(rt);
        let ninner = resolve_qualified_names_in_stype_inner(py, inner, qualified_scope, unqualified_scope, constructor_defs)?;
        let nrefn = resolve_qualified_names_in_sterm_inner(py, refn, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_srefinedtype(py, name, ninner, nrefn, loc);
    }

    if let Ok(at) = b.downcast::<SAbstractionType>() {
        let at = at.borrow();
        let var_name = at.var_name.clone_ref(py);
        let var_type = at.var_type.clone_ref(py);
        let body_type = at.type_.clone_ref(py);
        let loc = at.loc.clone_ref(py);
        let mult = at.multiplicity.clone_ref(py);
        drop(at);
        let nvt = resolve_qualified_names_in_stype_inner(py, var_type, qualified_scope, unqualified_scope, constructor_defs)?;
        let nbt = resolve_qualified_names_in_stype_inner(py, body_type, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_sabstractiontype(py, var_name, nvt, nbt, loc, mult);
    }

    if let Ok(tp) = b.downcast::<STypePolymorphism>() {
        let tp = tp.borrow();
        let name = tp.name.clone_ref(py);
        let kind = tp.kind.clone_ref(py);
        let body = tp.body.clone_ref(py);
        let loc = tp.loc.clone_ref(py);
        drop(tp);
        let nb = resolve_qualified_names_in_stype_inner(py, body, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_stypepolymorphism(py, name, kind, nb, loc);
    }

    if let Ok(rp) = b.downcast::<SRefinementPolymorphism>() {
        let rp = rp.borrow();
        let name = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        let loc = rp.loc.clone_ref(py);
        drop(rp);
        let ns = resolve_qualified_names_in_stype_inner(py, sort, qualified_scope, unqualified_scope, constructor_defs)?;
        let nb = resolve_qualified_names_in_stype_inner(py, body, qualified_scope, unqualified_scope, constructor_defs)?;
        return mk_srefinement_polymorphism(py, name, ns, nb, loc);
    }

    if let Ok(tc) = b.downcast::<STypeConstructor>() {
        let tc = tc.borrow();
        let name = tc.name.clone_ref(py);
        let args = tc.args.clone_ref(py);
        let loc = tc.loc.clone_ref(py);
        drop(tc);
        let new_args = PyList::empty_bound(py);
        let args_b = args.bind(py);
        for i in 0..args_b.len() {
            let a = args_b.get_item(i)?.unbind();
            let na = resolve_qualified_names_in_stype_inner(py, a, qualified_scope, unqualified_scope, constructor_defs)?;
            new_args.append(na)?;
        }
        return mk_stypeconstructor(py, name, new_args.unbind(), loc);
    }

    Ok(ty)
}

#[pyfunction]
#[pyo3(signature = (ty, qualified_scope, unqualified_scope, constructor_defs = None))]
pub fn resolve_qualified_names_in_stype(
    py: Python<'_>,
    ty: PyObject,
    qualified_scope: Py<PyDict>,
    unqualified_scope: Py<PyDict>,
    constructor_defs: Option<Py<PyDict>>,
) -> PyResult<PyObject> {
    let qs = qualified_scope.bind(py).clone();
    let us = unqualified_scope.bind(py).clone();
    let cd = constructor_defs.as_ref().map(|d| d.bind(py).clone());
    resolve_qualified_names_in_stype_inner(py, ty, &qs, &us, cd.as_ref())
}

#[pyfunction]
#[pyo3(signature = (d, qualified_scope, unqualified_scope, constructor_defs = None))]
pub fn resolve_qualified_names_in_definition(
    py: Python<'_>,
    d: Py<Definition>,
    qualified_scope: Py<PyDict>,
    unqualified_scope: Py<PyDict>,
    constructor_defs: Option<Py<PyDict>>,
) -> PyResult<Py<Definition>> {
    let qs = qualified_scope.bind(py).clone();
    let us = unqualified_scope.bind(py).clone();
    let cd = constructor_defs.as_ref().map(|d| d.bind(py).clone());
    let cd_ref = cd.as_ref();

    let db = d.borrow(py);
    let new_body = resolve_qualified_names_in_sterm_inner(py, db.body.clone_ref(py), &qs, &us, cd_ref)?;

    let args = db.args.clone_ref(py);
    let new_args = PyList::empty_bound(py);
    let args_b = args.bind(py);
    for i in 0..args_b.len() {
        let pair = args_b.get_item(i)?;
        let name = pair.get_item(0)?.unbind();
        let ty = pair.get_item(1)?.unbind();
        let nty = resolve_qualified_names_in_stype_inner(py, ty, &qs, &us, cd_ref)?;
        let new_pair = PyTuple::new_bound(py, &[name, nty]).unbind();
        new_args.append(new_pair)?;
    }

    let new_type = resolve_qualified_names_in_stype_inner(py, db.type_.clone_ref(py), &qs, &us, cd_ref)?;

    // Decorators
    let new_decorators = PyList::empty_bound(py);
    let decs = db.decorators.clone_ref(py);
    let decs_b = decs.bind(py);
    for i in 0..decs_b.len() {
        let dec = decs_b.get_item(i)?;
        let dec = dec.downcast::<Decorator>()?;
        let dec = dec.borrow();
        let macro_args = dec.macro_args.clone_ref(py);
        let named_args = dec.named_args.clone_ref(py);
        let dec_name = dec.name.clone_ref(py);
        let dec_loc = dec.loc.clone_ref(py);
        drop(dec);

        // macro_args
        let new_macro = PyList::empty_bound(py);
        let ma_b = macro_args.bind(py);
        for j in 0..ma_b.len() {
            let a = ma_b.get_item(j)?.unbind();
            let na = resolve_qualified_names_in_sterm_inner(py, a, &qs, &us, cd_ref)?;
            new_macro.append(na)?;
        }
        // named_args dict[Name, STerm]
        let new_named = PyDict::new_bound(py);
        let na_b = named_args.bind(py);
        if let Ok(d) = na_b.downcast::<PyDict>() {
            for (k, v) in d.iter() {
                let nv = resolve_qualified_names_in_sterm_inner(py, v.unbind(), &qs, &us, cd_ref)?;
                new_named.set_item(k, nv)?;
            }
        }
        let new_dec = Py::new(
            py,
            (
                Decorator {
                    name: dec_name,
                    macro_args: new_macro.unbind(),
                    named_args: new_named.unbind().into_any(),
                    loc: dec_loc,
                },
                Node,
            ),
        )?;
        new_decorators.append(new_dec)?;
    }

    let new_def = Py::new(
        py,
        (
            Definition {
                name: db.name.clone_ref(py),
                foralls: db.foralls.clone_ref(py),
                args: new_args.unbind(),
                type_: new_type,
                body: new_body,
                decorators: new_decorators.unbind(),
                rforalls: db.rforalls.clone_ref(py),
                decreasing_by: db.decreasing_by.clone_ref(py),
                arg_multiplicities: db.arg_multiplicities.clone_ref(py),
                loc: db.loc.clone_ref(py),
            },
            Node,
        ),
    )?;
    Ok(new_def)
}

// =============================================================================
// determine_main_function
// =============================================================================

#[pyfunction]
#[pyo3(signature = (p, is_main_hole = None))]
pub fn determine_main_function(
    py: Python<'_>,
    p: Py<Program>,
    is_main_hole: Option<PyObject>,
) -> PyResult<PyObject> {
    // The Python signature accepted ``is_main_hole: bool = True`` but callers in
    // practice pass arbitrary truthy/falsy values (None, dicts), and the original
    // Python code only ever inspects truthiness. Mirror that here.
    let is_main_hole = match is_main_hole {
        None => false,
        Some(obj) => obj.bind(py).is_truthy().unwrap_or(false),
    };
    let pb = p.borrow(py);
    let defs = pb.definitions.clone_ref(py);
    drop(pb);
    let defs_b = defs.bind(py);
    for i in 0..defs_b.len() {
        let d = defs_b.get_item(i)?;
        let d = d.downcast::<Definition>()?;
        let d = d.borrow();
        let nm = d.name.clone_ref(py);
        let nb = nm.borrow(py);
        if nb.name == "main" {
            let id = nb.id;
            drop(nb);
            let new_name = mk_name(py, "main", id)?;
            let var = mk_svar(py, new_name, default_loc(py))?;
            // SApplication(SVar(Name("main", id)), SLiteral(1, type=st_int))
            let one = py.eval_bound("1", None, None)?.unbind();
            let lit = Py::new(
                py,
                (SLiteral { value: one, type_: st_int(py)?, loc: default_loc(py) }, STerm),
            )?
            .into_any();
            return mk_sapplication(py, var, lit, default_loc(py));
        }
    }
    if is_main_hole {
        let nm = mk_name(py, "main", 0)?;
        return mk_shole(py, nm, default_loc(py));
    }
    let one = py.eval_bound("1", None, None)?.unbind();
    let lit = Py::new(py, (SLiteral { value: one, type_: st_int(py)?, loc: default_loc(py) }, STerm))?;
    Ok(lit.into_any())
}

// =============================================================================
// type_of_definition / convert_definition_to_srec
// =============================================================================

fn make_type_of_definition(py: Python<'_>, d: &Definition) -> PyResult<PyObject> {
    let mut ntype = d.type_.clone_ref(py);
    let args_b = d.args.bind(py);
    let n_args = args_b.len();
    let loc = d.loc.clone_ref(py);
    // reversed
    for i in 0..n_args {
        let idx = n_args - 1 - i;
        let pair = args_b.get_item(idx)?;
        let name: Py<Name> = pair.get_item(0)?.downcast::<Name>()?.clone().unbind();
        let aty: PyObject = pair.get_item(1)?.unbind();
        let mult_index = idx;
        let am = d.arg_multiplicities.bind(py);
        let mlen: usize = am.len().unwrap_or(0);
        let mult = if mult_index < mlen {
            am.get_item(mult_index)?.unbind()
        } else {
            crate::types::default_multiplicity(py)
        };
        ntype = mk_sabstractiontype(py, name, aty, ntype, loc.clone_ref(py), mult)?;
    }
    let rfs_b = d.rforalls.bind(py);
    let rfslen = rfs_b.len();
    for i in 0..rfslen {
        let idx = rfslen - 1 - i;
        let tup = rfs_b.get_item(idx)?;
        let name: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
        let sort = tup.get_item(1)?.unbind();
        ntype = mk_srefinement_polymorphism(py, name, sort, ntype, loc.clone_ref(py))?;
    }
    let foralls_b = d.foralls.bind(py);
    let flen = foralls_b.len();
    for i in 0..flen {
        let idx = flen - 1 - i;
        let tup = foralls_b.get_item(idx)?;
        let name: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
        let kind = tup.get_item(1)?.unbind();
        ntype = mk_stypepolymorphism(py, name, kind, ntype, loc.clone_ref(py))?;
    }
    Ok(ntype)
}

#[pyfunction]
pub fn type_of_definition(py: Python<'_>, d: Py<Definition>) -> PyResult<PyObject> {
    let db = d.borrow(py);
    make_type_of_definition(py, &db)
}

#[pyfunction]
pub fn convert_definition_to_srec(
    py: Python<'_>,
    prog: PyObject,
    d: Py<Definition>,
) -> PyResult<PyObject> {
    let d = definition_with_inferred_decreasing(py, d)?;
    let db = d.borrow(py);
    let dname = db.name.clone_ref(py);
    let loc = db.loc.clone_ref(py);

    let mut ntype = db.type_.clone_ref(py);
    let mut nbody = db.body.clone_ref(py);

    let args_b = db.args.bind(py);
    let n_args = args_b.len();
    for i in 0..n_args {
        let idx = n_args - 1 - i;
        let pair = args_b.get_item(idx)?;
        let name: Py<Name> = pair.get_item(0)?.downcast::<Name>()?.clone().unbind();
        let aty: PyObject = pair.get_item(1)?.unbind();
        let am = db.arg_multiplicities.bind(py);
        let mlen: usize = am.len().unwrap_or(0);
        let mult = if idx < mlen {
            am.get_item(idx)?.unbind()
        } else {
            crate::types::default_multiplicity(py)
        };
        ntype = mk_sabstractiontype(py, name.clone_ref(py), aty, ntype, loc.clone_ref(py), mult)?;
        nbody = mk_sabstraction(py, name, nbody, loc.clone_ref(py))?;
    }

    let rfs_b = db.rforalls.bind(py);
    let rfslen = rfs_b.len();
    for i in 0..rfslen {
        let idx = rfslen - 1 - i;
        let tup = rfs_b.get_item(idx)?;
        let name: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
        let sort: PyObject = tup.get_item(1)?.unbind();
        ntype = mk_srefinement_polymorphism(py, name.clone_ref(py), sort.clone_ref(py), ntype, loc.clone_ref(py))?;
        nbody = mk_srefinement_abstraction(py, name, sort, nbody, loc.clone_ref(py))?;
    }

    let foralls_b = db.foralls.bind(py);
    let flen = foralls_b.len();
    for i in 0..flen {
        let idx = flen - 1 - i;
        let tup = foralls_b.get_item(idx)?;
        let name: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
        let kind: PyObject = tup.get_item(1)?.unbind();
        ntype = mk_stypepolymorphism(py, name.clone_ref(py), kind.clone_ref(py), ntype, loc.clone_ref(py))?;
        nbody = mk_stypeabstraction(py, name, kind, nbody, loc.clone_ref(py))?;
    }

    let decr = db.decreasing_by.clone_ref(py);
    let decr_b = decr.bind(py);
    let mut decr_vec: Vec<PyObject> = Vec::with_capacity(decr_b.len());
    for i in 0..decr_b.len() {
        decr_vec.push(decr_b.get_item(i)?.unbind());
    }
    let decr_tuple = PyTuple::new_bound(py, decr_vec).unbind();

    let mult = crate::types::default_multiplicity(py);

    let out = mk_srec(py, dname, ntype, nbody, prog, decr_tuple, loc, mult)?;
    Ok(out)
}

// =============================================================================
// update_program_and_context
// =============================================================================

#[pyfunction]
pub fn update_program_and_context(
    py: Python<'_>,
    prog: PyObject,
    defs: Py<PyList>,
    ctx: Py<ElaborationTypingContext>,
) -> PyResult<(Py<ElaborationTypingContext>, PyObject)> {
    let mut prog = prog;
    let defs_b = defs.bind(py);
    let dlen = defs_b.len();
    for i in 0..dlen {
        let idx = dlen - 1 - i;
        let dany = defs_b.get_item(idx)?;
        let dpy = dany.downcast::<Definition>()?;
        let d = dpy.borrow();
        let body = d.body.clone_ref(py);
        let name = d.name.clone_ref(py);
        // Match body: SVar(Name("uninterpreted", _))
        let bb = body.bind(py);
        let mut is_uninterp = false;
        if let Ok(sv) = bb.downcast::<SVar>() {
            let sv = sv.borrow();
            if sv.name.borrow(py).name == "uninterpreted" {
                is_uninterp = true;
            }
        }
        drop(d);
        if is_uninterp {
            // Make ElabUninterpretedBinder
            let dpy_b = dpy.borrow();
            let ty = make_type_of_definition(py, &dpy_b)?;
            drop(dpy_b);
            let binder = Py::new(
                py,
                (
                    ElabUninterpretedBinder { name, type_: ty },
                    ElabTypingContextEntry,
                ),
            )?;
            let ctx_b = ctx.borrow(py);
            ctx_b.entries.bind(py).append(binder)?;
        } else {
            // Call convert_definition_to_srec(prog, d)
            let dpy_obj: Py<Definition> = dpy.clone().unbind();
            prog = convert_definition_to_srec(py, prog, dpy_obj)?;
        }
    }
    Ok((ctx, prog))
}

// =============================================================================
// replace_concrete_types
// =============================================================================

#[pyfunction]
pub fn replace_concrete_types(
    py: Python<'_>,
    t: PyObject,
    etctx: Py<ElaborationTypingContext>,
    types: Py<PyList>,
) -> PyResult<(PyObject, Py<ElaborationTypingContext>)> {
    let types_b = types.bind(py);
    let mut tnames: Vec<Py<Name>> = Vec::with_capacity(types_b.len());
    for i in 0..types_b.len() {
        let n = types_b.get_item(i)?;
        let nn: Py<Name> = n.downcast::<Name>()?.clone().unbind();
        tnames.push(nn);
    }

    let mut t = t;
    for name in &tnames {
        let stc = mk_stypeconstructor(
            py,
            name.clone_ref(py),
            PyList::empty_bound(py).unbind(),
            default_loc(py),
        )?;
        t = substitution_svartype_in_sterm(py, t, stc, name.clone_ref(py))?;
    }

    // Rebuild context entries: substitute STypeVar -> STypeConstructor in types of ElabVariableBinder/ElabUninterpretedBinder
    let ctx_b = etctx.borrow(py);
    let entries = ctx_b.entries.clone_ref(py);
    let ctype_dict = ctx_b.constructor_to_type.clone_ref(py);
    let cdefs_dict = ctx_b.constructor_defs.clone_ref(py);
    drop(ctx_b);

    let new_entries = PyList::empty_bound(py);
    let entries_b = entries.bind(py);
    for i in 0..entries_b.len() {
        let e = entries_b.get_item(i)?;
        if let Ok(vb) = e.downcast::<ElabVariableBinder>() {
            let vb = vb.borrow();
            let vname = vb.name.clone_ref(py);
            let mut nty = vb.type_.clone_ref(py);
            drop(vb);
            for name in &tnames {
                let stc = mk_stypeconstructor(
                    py,
                    name.clone_ref(py),
                    PyList::empty_bound(py).unbind(),
                    default_loc(py),
                )?;
                nty = substitute_svartype_in_stype(py, nty, stc, name.clone_ref(py))?;
            }
            let nb = Py::new(
                py,
                (
                    ElabVariableBinder { name: vname, type_: nty },
                    ElabTypingContextEntry,
                ),
            )?;
            new_entries.append(nb)?;
        } else if let Ok(ub) = e.downcast::<ElabUninterpretedBinder>() {
            let ub = ub.borrow();
            let vname = ub.name.clone_ref(py);
            let mut nty = ub.type_.clone_ref(py);
            drop(ub);
            for name in &tnames {
                let stc = mk_stypeconstructor(
                    py,
                    name.clone_ref(py),
                    PyList::empty_bound(py).unbind(),
                    default_loc(py),
                )?;
                nty = substitute_svartype_in_stype(py, nty, stc, name.clone_ref(py))?;
            }
            let nb = Py::new(
                py,
                (
                    ElabUninterpretedBinder { name: vname, type_: nty },
                    ElabTypingContextEntry,
                ),
            )?;
            new_entries.append(nb)?;
        } else {
            new_entries.append(e)?;
        }
    }

    let new_ctx = Py::new(
        py,
        ElaborationTypingContext {
            entries: new_entries.unbind(),
            constructor_to_type: ctype_dict,
            constructor_defs: cdefs_dict,
        },
    )?;
    Ok((t, new_ctx))
}

// =============================================================================
// introduce_forall_in_types
// =============================================================================

fn get_type_vars_collect(
    py: Python<'_>,
    ty: &PyObject,
    out: &mut Vec<(String, i64)>,
    seen: &mut HashSet<(String, i64)>,
) -> PyResult<()> {
    let b = ty.bind(py);
    if let Ok(tv) = b.downcast::<STypeVar>() {
        let tv = tv.borrow();
        let n = tv.name.borrow(py);
        let key = (n.name.clone(), n.id);
        if !seen.contains(&key) {
            seen.insert(key.clone());
            out.push(key);
        }
        return Ok(());
    }
    if let Ok(at) = b.downcast::<SAbstractionType>() {
        let at = at.borrow();
        let vt = at.var_type.clone_ref(py);
        let rt = at.type_.clone_ref(py);
        drop(at);
        get_type_vars_collect(py, &vt, out, seen)?;
        get_type_vars_collect(py, &rt, out, seen)?;
        return Ok(());
    }
    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let rt = rt.borrow();
        let inner = rt.type_.clone_ref(py);
        drop(rt);
        return get_type_vars_collect(py, &inner, out, seen);
    }
    if let Ok(tp) = b.downcast::<STypePolymorphism>() {
        let tp = tp.borrow();
        let nm = tp.name.borrow(py).name.clone();
        let body = tp.body.clone_ref(py);
        drop(tp);
        let mut inner_out: Vec<(String, i64)> = Vec::new();
        let mut inner_seen: HashSet<(String, i64)> = HashSet::new();
        get_type_vars_collect(py, &body, &mut inner_out, &mut inner_seen)?;
        for k in inner_out {
            if k.0 != nm && !seen.contains(&k) {
                seen.insert(k.clone());
                out.push(k);
            }
        }
        return Ok(());
    }
    if let Ok(rp) = b.downcast::<SRefinementPolymorphism>() {
        let rp = rp.borrow();
        let body = rp.body.clone_ref(py);
        drop(rp);
        return get_type_vars_collect(py, &body, out, seen);
    }
    if let Ok(tc) = b.downcast::<STypeConstructor>() {
        let tc = tc.borrow();
        let args = tc.args.clone_ref(py);
        drop(tc);
        let args_b = args.bind(py);
        for i in 0..args_b.len() {
            let a = args_b.get_item(i)?.unbind();
            get_type_vars_collect(py, &a, out, seen)?;
        }
        return Ok(());
    }
    // Default: unknown — best effort
    Ok(())
}

#[pyfunction]
pub fn introduce_forall_in_types(
    py: Python<'_>,
    defs: Py<PyList>,
    type_decls: Py<PyList>,
) -> PyResult<Py<PyList>> {
    // collect declared type names
    let mut declared: HashSet<String> = HashSet::new();
    let td_b = type_decls.bind(py);
    for i in 0..td_b.len() {
        let td = td_b.get_item(i)?;
        let name = td.getattr("name")?;
        let n: Py<Name> = name.downcast::<Name>()?.clone().unbind();
        declared.insert(name_str(py, &n));
    }

    let out = PyList::empty_bound(py);
    let defs_b = defs.bind(py);
    for i in 0..defs_b.len() {
        let dany = defs_b.get_item(i)?;
        let dpy = dany.downcast::<Definition>()?;
        let d = dpy.borrow();
        let foralls = d.foralls.clone_ref(py);
        let args = d.args.clone_ref(py);
        let rtype = d.type_.clone_ref(py);

        // bound_tvars = {n.name for (n, _) in foralls}
        let mut bound: HashSet<String> = HashSet::new();
        let foralls_b = foralls.bind(py);
        for j in 0..foralls_b.len() {
            let tup = foralls_b.get_item(j)?;
            let nm: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            bound.insert(name_str(py, &nm));
        }

        // Walk through arg types + rtype, collect free type vars.
        let mut new_foralls: Vec<Py<Name>> = Vec::new();
        let mut new_foralls_keys: HashSet<(String, i64)> = HashSet::new();
        let args_b = args.bind(py);
        for j in 0..args_b.len() {
            let pair = args_b.get_item(j)?;
            let ty = pair.get_item(1)?.unbind();
            let mut tvs: Vec<(String, i64)> = Vec::new();
            let mut seen: HashSet<(String, i64)> = HashSet::new();
            get_type_vars_collect(py, &ty, &mut tvs, &mut seen)?;
            for (tname, tid) in tvs {
                if !declared.contains(&tname) && !bound.contains(&tname) && !new_foralls_keys.contains(&(tname.clone(), tid)) {
                    new_foralls_keys.insert((tname.clone(), tid));
                    new_foralls.push(mk_name(py, &tname, tid)?);
                }
            }
        }
        let mut tvs: Vec<(String, i64)> = Vec::new();
        let mut seen: HashSet<(String, i64)> = HashSet::new();
        get_type_vars_collect(py, &rtype, &mut tvs, &mut seen)?;
        for (tname, tid) in tvs {
            if !declared.contains(&tname) && !bound.contains(&tname) && !new_foralls_keys.contains(&(tname.clone(), tid)) {
                new_foralls_keys.insert((tname.clone(), tid));
                new_foralls.push(mk_name(py, &tname, tid)?);
            }
        }

        // Build the new foralls list = existing + new
        let new_foralls_list = PyList::empty_bound(py);
        for j in 0..foralls_b.len() {
            new_foralls_list.append(foralls_b.get_item(j)?)?;
        }
        let base_kind = Py::new(py, (BaseKind, Kind))?;
        for n in new_foralls {
            let pair = PyTuple::new_bound(py, &[n.into_any(), base_kind.clone_ref(py).into_any()]).unbind();
            new_foralls_list.append(pair)?;
        }

        let new_def = Py::new(
            py,
            (
                Definition {
                    name: d.name.clone_ref(py),
                    foralls: new_foralls_list.unbind(),
                    args: d.args.clone_ref(py),
                    type_: d.type_.clone_ref(py),
                    body: d.body.clone_ref(py),
                    decorators: d.decorators.clone_ref(py),
                    rforalls: d.rforalls.clone_ref(py),
                    decreasing_by: d.decreasing_by.clone_ref(py),
                    arg_multiplicities: d.arg_multiplicities.clone_ref(py),
                    loc: d.loc.clone_ref(py),
                },
                Node,
            ),
        )?;
        drop(d);
        out.append(new_def)?;
    }
    Ok(out.unbind())
}

// =============================================================================
// _collect_implicit_refinement_params  +  introduce_rforall_in_types
// =============================================================================

/// acc: dict[Name as (string,id)] -> SType.
type AccMap = Vec<(Py<Name>, PyObject)>;

fn acc_get<'a>(py: Python<'_>, acc: &'a AccMap, key: &Py<Name>) -> Option<&'a PyObject> {
    for (k, v) in acc.iter() {
        if pyname_eq(py, k, key) {
            return Some(v);
        }
    }
    None
}

fn acc_insert(py: Python<'_>, acc: &mut AccMap, key: Py<Name>, value: PyObject) {
    for entry in acc.iter_mut() {
        if pyname_eq(py, &entry.0, &key) {
            entry.1 = value;
            return;
        }
    }
    acc.push((key, value));
}

fn name_in_set(py: Python<'_>, set: &HashSet<(String, i64)>, n: &Py<Name>) -> bool {
    let b = n.borrow(py);
    set.contains(&(b.name.clone(), b.id))
}

fn nkey(py: Python<'_>, n: &Py<Name>) -> (String, i64) {
    let b = n.borrow(py);
    (b.name.clone(), b.id)
}

fn collect_implicit_refinement_params(
    py: Python<'_>,
    ty: &PyObject,
    bound_rho: &HashSet<(String, i64)>,
    acc: &mut AccMap,
) -> PyResult<()> {
    let b = ty.bind(py);
    if let Ok(rp) = b.downcast::<SRefinementPolymorphism>() {
        let rp = rp.borrow();
        let rname = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        drop(rp);
        collect_implicit_refinement_params(py, &sort, bound_rho, acc)?;
        let mut new_bound = bound_rho.clone();
        new_bound.insert(nkey(py, &rname));
        collect_implicit_refinement_params(py, &body, &new_bound, acc)?;
        return Ok(());
    }
    if let Ok(tp) = b.downcast::<STypePolymorphism>() {
        let tp = tp.borrow();
        let body = tp.body.clone_ref(py);
        drop(tp);
        return collect_implicit_refinement_params(py, &body, bound_rho, acc);
    }
    if let Ok(at) = b.downcast::<SAbstractionType>() {
        let at = at.borrow();
        let vt = at.var_type.clone_ref(py);
        let rt = at.type_.clone_ref(py);
        drop(at);
        collect_implicit_refinement_params(py, &vt, bound_rho, acc)?;
        return collect_implicit_refinement_params(py, &rt, bound_rho, acc);
    }
    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let rt = rt.borrow();
        let binder = rt.name.clone_ref(py);
        let base = rt.type_.clone_ref(py);
        let refn = rt.refinement.clone_ref(py);
        drop(rt);
        collect_implicit_refinement_params(py, &base, bound_rho, acc)?;
        // refinement match: SApplication(SVar(p), SVar(b)) where b == binder and p not in bound_rho
        let rb = refn.bind(py);
        if let Ok(sapp) = rb.downcast::<SApplication>() {
            let sapp = sapp.borrow();
            let fun = sapp.fun.clone_ref(py);
            let arg = sapp.arg.clone_ref(py);
            drop(sapp);
            let fb = fun.bind(py);
            let ab = arg.bind(py);
            if let (Ok(p), Ok(bvar)) = (fb.downcast::<SVar>(), ab.downcast::<SVar>()) {
                let p_name = p.borrow().name.clone_ref(py);
                let b_name = bvar.borrow().name.clone_ref(py);
                if pyname_eq(py, &b_name, &binder) && !name_in_set(py, bound_rho, &p_name) {
                    if let Some(existing) = acc_get(py, acc, &p_name) {
                        let eq = type_equality(py, existing.clone_ref(py), base.clone_ref(py), None)?;
                        if !eq {
                            return Err(PyTypeError::new_err(format!(
                                "Inconsistent sorts for implicit refinement parameter {}: {} vs {}",
                                p_name.borrow(py).name,
                                existing.bind(py).str()?,
                                base.bind(py).str()?
                            )));
                        }
                    } else {
                        acc_insert(py, acc, p_name, base);
                    }
                }
            }
        }
        return Ok(());
    }
    if let Ok(tc) = b.downcast::<STypeConstructor>() {
        let tc = tc.borrow();
        let args = tc.args.clone_ref(py);
        drop(tc);
        let args_b = args.bind(py);
        for i in 0..args_b.len() {
            let a = args_b.get_item(i)?.unbind();
            collect_implicit_refinement_params(py, &a, bound_rho, acc)?;
        }
        return Ok(());
    }
    if b.downcast::<STypeVar>().is_ok() {
        return Ok(());
    }
    Err(PyAssertionError::new_err(format!(
        "_collect_implicit_refinement_params: unhandled {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

#[pyfunction]
pub fn introduce_rforall_in_types(py: Python<'_>, defs: Py<PyList>) -> PyResult<Py<PyList>> {
    let out = PyList::empty_bound(py);
    let defs_b = defs.bind(py);
    for i in 0..defs_b.len() {
        let dany = defs_b.get_item(i)?;
        let dpy = dany.downcast::<Definition>()?;
        let d = dpy.borrow();
        let foralls = d.foralls.clone_ref(py);
        let args = d.args.clone_ref(py);
        let rtype = d.type_.clone_ref(py);
        let body = d.body.clone_ref(py);
        let decorators = d.decorators.clone_ref(py);
        let rforalls = d.rforalls.clone_ref(py);
        let decreasing_by = d.decreasing_by.clone_ref(py);
        let arg_multiplicities = d.arg_multiplicities.clone_ref(py);
        let loc = d.loc.clone_ref(py);
        let name = d.name.clone_ref(py);
        drop(d);

        let mut acc: AccMap = Vec::new();
        let args_b = args.bind(py);
        for j in 0..args_b.len() {
            let pair = args_b.get_item(j)?;
            let ty = pair.get_item(1)?.unbind();
            collect_implicit_refinement_params(py, &ty, &HashSet::new(), &mut acc)?;
        }
        collect_implicit_refinement_params(py, &rtype, &HashSet::new(), &mut acc)?;

        // existing = {p for (p, _) in rforalls}
        let rf_b = rforalls.bind(py);
        let mut existing: Vec<Py<Name>> = Vec::new();
        for j in 0..rf_b.len() {
            let tup = rf_b.get_item(j)?;
            let p: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            existing.push(p);
        }

        // new entries: those in acc not in existing
        let mut new_entries: Vec<(Py<Name>, PyObject)> = Vec::new();
        for (p, s) in acc.iter() {
            let in_existing = existing.iter().any(|e| pyname_eq(py, e, p));
            if !in_existing {
                new_entries.push((p.clone_ref(py), s.clone_ref(py)));
            }
        }

        // merged_rforalls = rforalls + new_entries (as list of tuples)
        let merged_list = PyList::empty_bound(py);
        for j in 0..rf_b.len() {
            merged_list.append(rf_b.get_item(j)?)?;
        }
        for (p, s) in new_entries.iter() {
            let tup = PyTuple::new_bound(py, &[p.clone_ref(py).into_any(), s.clone_ref(py)]).unbind();
            merged_list.append(tup)?;
        }

        let mut final_rtype = rtype;
        let mut final_rforalls = merged_list.unbind();

        let final_rforalls_len = final_rforalls.bind(py).len();
        if final_rforalls_len > 0 {
            // If rtype is STypePolymorphism(tn, tk, tbody), splice rforalls inside.
            let rt_b = final_rtype.bind(py);
            if let Ok(tp) = rt_b.downcast::<STypePolymorphism>() {
                let tp = tp.borrow();
                let tn = tp.name.clone_ref(py);
                let tk = tp.kind.clone_ref(py);
                let tbody = tp.body.clone_ref(py);
                let rtype_loc = tp.loc.clone_ref(py);
                drop(tp);

                let mut inner = tbody;
                let mr_b = final_rforalls.bind(py);
                for j in 0..mr_b.len() {
                    let tup = mr_b.get_item(j)?;
                    let pname: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
                    let psort: PyObject = tup.get_item(1)?.unbind();
                    inner = mk_srefinement_polymorphism(py, pname, psort, inner, loc.clone_ref(py))?;
                }
                final_rtype = mk_stypepolymorphism(py, tn, tk, inner, rtype_loc)?;
                final_rforalls = PyList::empty_bound(py).unbind();
            }
        }

        let new_def = Py::new(
            py,
            (
                Definition {
                    name,
                    foralls,
                    args,
                    type_: final_rtype,
                    body,
                    decorators,
                    rforalls: final_rforalls,
                    decreasing_by,
                    arg_multiplicities,
                    loc,
                },
                Node,
            ),
        )?;
        out.append(new_def)?;
    }
    Ok(out.unbind())
}

// =============================================================================
// Inductive helpers
// =============================================================================

fn merge_inductive_rforalls(
    py: Python<'_>,
    dtype_rfs: &Py<PyList>,
    local_rfs: &Py<PyList>,
) -> PyResult<Py<PyList>> {
    let dt_b = dtype_rfs.bind(py);
    let mut seen: HashSet<(String, i64)> = HashSet::new();
    let out = PyList::empty_bound(py);
    for i in 0..dt_b.len() {
        let tup = dt_b.get_item(i)?;
        let nm: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
        seen.insert(nkey(py, &nm));
        out.append(tup)?;
    }
    let lc_b = local_rfs.bind(py);
    for i in 0..lc_b.len() {
        let tup = lc_b.get_item(i)?;
        let nm: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
        if !seen.contains(&nkey(py, &nm)) {
            out.append(tup)?;
        }
    }
    Ok(out.unbind())
}

fn eligible_refinement_base_for_inductive(
    py: Python<'_>,
    ind: &InductiveDecl,
    base: &PyObject,
) -> PyResult<bool> {
    let b = base.bind(py);
    if let Ok(tc) = b.downcast::<STypeConstructor>() {
        let tc = tc.borrow();
        let tcn = tc.name.clone_ref(py);
        drop(tc);
        if pyname_eq(py, &tcn, &ind.name) {
            return Ok(true);
        }
        let ind_n = ind.name.borrow(py);
        if tcn.borrow(py).name == ind_n.name {
            return Ok(true);
        }
        return Ok(false);
    }
    if let Ok(tv) = b.downcast::<STypeVar>() {
        let tv = tv.borrow();
        let tvn = tv.name.borrow(py);
        let ind_n = ind.name.borrow(py);
        if tvn.name == ind_n.name {
            return Ok(true);
        }
        drop(tvn);
        drop(ind_n);
        let args = ind.args.clone_ref(py);
        let args_b = args.bind(py);
        for i in 0..args_b.len() {
            let an: Py<Name> = args_b.get_item(i)?.downcast::<Name>()?.clone().unbind();
            if an.borrow(py).name == tv.name.borrow(py).name {
                return Ok(true);
            }
        }
        return Ok(false);
    }
    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let rt = rt.borrow();
        let inner = rt.type_.clone_ref(py);
        drop(rt);
        return eligible_refinement_base_for_inductive(py, ind, &inner);
    }
    Ok(false)
}

fn collect_implicit_refinement_params_for_inductive(
    py: Python<'_>,
    ind: &InductiveDecl,
    ty: &PyObject,
    bound_rho: &HashSet<(String, i64)>,
    acc: &mut AccMap,
) -> PyResult<()> {
    let b = ty.bind(py);
    if let Ok(rp) = b.downcast::<SRefinementPolymorphism>() {
        let rp = rp.borrow();
        let rname = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        drop(rp);
        collect_implicit_refinement_params_for_inductive(py, ind, &sort, bound_rho, acc)?;
        let mut nb = bound_rho.clone();
        nb.insert(nkey(py, &rname));
        return collect_implicit_refinement_params_for_inductive(py, ind, &body, &nb, acc);
    }
    if let Ok(tp) = b.downcast::<STypePolymorphism>() {
        let tp = tp.borrow();
        let body = tp.body.clone_ref(py);
        drop(tp);
        return collect_implicit_refinement_params_for_inductive(py, ind, &body, bound_rho, acc);
    }
    if let Ok(at) = b.downcast::<SAbstractionType>() {
        let at = at.borrow();
        let vt = at.var_type.clone_ref(py);
        let rt = at.type_.clone_ref(py);
        drop(at);
        collect_implicit_refinement_params_for_inductive(py, ind, &vt, bound_rho, acc)?;
        return collect_implicit_refinement_params_for_inductive(py, ind, &rt, bound_rho, acc);
    }
    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let rt = rt.borrow();
        let binder = rt.name.clone_ref(py);
        let base = rt.type_.clone_ref(py);
        let refn = rt.refinement.clone_ref(py);
        drop(rt);
        collect_implicit_refinement_params_for_inductive(py, ind, &base, bound_rho, acc)?;
        let rb = refn.bind(py);
        if let Ok(sapp) = rb.downcast::<SApplication>() {
            let sapp = sapp.borrow();
            let fun = sapp.fun.clone_ref(py);
            let arg = sapp.arg.clone_ref(py);
            drop(sapp);
            let fb = fun.bind(py);
            let ab = arg.bind(py);
            if let (Ok(pv), Ok(bvar)) = (fb.downcast::<SVar>(), ab.downcast::<SVar>()) {
                let p_name = pv.borrow().name.clone_ref(py);
                let b_name = bvar.borrow().name.clone_ref(py);
                if pyname_eq(py, &b_name, &binder) && !name_in_set(py, bound_rho, &p_name) {
                    let eligible = eligible_refinement_base_for_inductive(py, ind, &base)?;
                    if !eligible {
                        // skip
                    } else if let Some(existing) = acc_get(py, acc, &p_name) {
                        let eq = type_equality(py, existing.clone_ref(py), base.clone_ref(py), None)?;
                        if !eq {
                            return Err(PyTypeError::new_err(format!(
                                "Inconsistent sorts for inferred datatype refinement {} on {}: {} vs {}",
                                p_name.borrow(py).name,
                                ind.name.borrow(py).name,
                                existing.bind(py).str()?,
                                base.bind(py).str()?
                            )));
                        }
                    } else {
                        acc_insert(py, acc, p_name, base);
                    }
                }
            }
        }
        return Ok(());
    }
    if let Ok(tc) = b.downcast::<STypeConstructor>() {
        let tc = tc.borrow();
        let args = tc.args.clone_ref(py);
        drop(tc);
        let args_b = args.bind(py);
        for i in 0..args_b.len() {
            let a = args_b.get_item(i)?.unbind();
            collect_implicit_refinement_params_for_inductive(py, ind, &a, bound_rho, acc)?;
        }
        return Ok(());
    }
    if b.downcast::<STypeVar>().is_ok() {
        return Ok(());
    }
    Err(PyAssertionError::new_err(format!(
        "_collect_implicit_refinement_params_for_inductive: unhandled {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

#[pyfunction]
pub fn infer_inductive_rforall_decls(py: Python<'_>, p: Py<Program>) -> PyResult<Py<Program>> {
    let pb = p.borrow(py);
    let imports = pb.imports.clone_ref(py);
    let type_decls = pb.type_decls.clone_ref(py);
    let inductive_decls = pb.inductive_decls.clone_ref(py);
    let definitions = pb.definitions.clone_ref(py);
    drop(pb);

    let new_inductive_decls = PyList::empty_bound(py);
    let ind_b = inductive_decls.bind(py);
    for i in 0..ind_b.len() {
        let indany = ind_b.get_item(i)?;
        let indpy = indany.downcast::<InductiveDecl>()?;
        let ind = indpy.borrow();
        let rfs_b = ind.rforalls.bind(py);
        if rfs_b.len() > 0 {
            drop(ind);
            new_inductive_decls.append(indany)?;
            continue;
        }

        let mut acc: AccMap = Vec::new();

        // Scan constructor args/return types
        let cons = ind.constructors.clone_ref(py);
        let cons_b = cons.bind(py);
        for j in 0..cons_b.len() {
            let c = cons_b.get_item(j)?;
            let cd = c.downcast::<Definition>()?;
            let cd = cd.borrow();
            let cargs = cd.args.clone_ref(py);
            let crtype = cd.type_.clone_ref(py);
            drop(cd);
            let ca_b = cargs.bind(py);
            for k in 0..ca_b.len() {
                let pair = ca_b.get_item(k)?;
                let aty = pair.get_item(1)?.unbind();
                collect_implicit_refinement_params_for_inductive(py, &ind, &aty, &HashSet::new(), &mut acc)?;
            }
            collect_implicit_refinement_params_for_inductive(py, &ind, &crtype, &HashSet::new(), &mut acc)?;
        }

        // Scan measure args/return types
        let meas = ind.measures.clone_ref(py);
        let meas_b = meas.bind(py);
        for j in 0..meas_b.len() {
            let m = meas_b.get_item(j)?;
            let md = m.downcast::<Definition>()?;
            let md = md.borrow();
            let margs = md.args.clone_ref(py);
            let mrtype = md.type_.clone_ref(py);
            drop(md);
            let ma_b = margs.bind(py);
            for k in 0..ma_b.len() {
                let pair = ma_b.get_item(k)?;
                let aty = pair.get_item(1)?.unbind();
                collect_implicit_refinement_params_for_inductive(py, &ind, &aty, &HashSet::new(), &mut acc)?;
            }
            collect_implicit_refinement_params_for_inductive(py, &ind, &mrtype, &HashSet::new(), &mut acc)?;
        }

        // Scan top-level definition arg/return types
        let defs_b = definitions.bind(py);
        for j in 0..defs_b.len() {
            let d = defs_b.get_item(j)?;
            let dd = d.downcast::<Definition>()?;
            let dd = dd.borrow();
            let dargs = dd.args.clone_ref(py);
            let drtype = dd.type_.clone_ref(py);
            drop(dd);
            let da_b = dargs.bind(py);
            for k in 0..da_b.len() {
                let pair = da_b.get_item(k)?;
                let aty = pair.get_item(1)?.unbind();
                collect_implicit_refinement_params_for_inductive(py, &ind, &aty, &HashSet::new(), &mut acc)?;
            }
            collect_implicit_refinement_params_for_inductive(py, &ind, &drtype, &HashSet::new(), &mut acc)?;
        }

        if acc.is_empty() {
            drop(ind);
            new_inductive_decls.append(indany)?;
        } else {
            // sort by (name.name, name.id)
            acc.sort_by(|a, b| {
                let an = a.0.borrow(py);
                let bn = b.0.borrow(py);
                (an.name.as_str(), an.id).cmp(&(bn.name.as_str(), bn.id))
            });
            let new_rfs = PyList::empty_bound(py);
            for (p, s) in &acc {
                let tup = PyTuple::new_bound(py, &[p.clone_ref(py).into_any(), s.clone_ref(py)]).unbind();
                new_rfs.append(tup)?;
            }
            let new_ind = Py::new(
                py,
                (
                    InductiveDecl {
                        name: ind.name.clone_ref(py),
                        args: ind.args.clone_ref(py),
                        rforalls: new_rfs.unbind(),
                        constructors: ind.constructors.clone_ref(py),
                        measures: ind.measures.clone_ref(py),
                        loc: ind.loc.clone_ref(py),
                    },
                    Node,
                ),
            )?;
            drop(ind);
            new_inductive_decls.append(new_ind)?;
        }
    }

    let new_p = Py::new(
        py,
        (
            Program {
                imports,
                type_decls,
                inductive_decls: new_inductive_decls.unbind(),
                definitions,
            },
            Node,
        ),
    )?;
    Ok(new_p)
}

// =============================================================================
// expand_inductive_decls
// =============================================================================

#[pyfunction]
pub fn expand_inductive_decls(py: Python<'_>, p: Py<Program>) -> PyResult<Py<Program>> {
    let pb = p.borrow(py);
    let imports = pb.imports.clone_ref(py);
    let existing_type_decls = pb.type_decls.clone_ref(py);
    let inductive_decls = pb.inductive_decls.clone_ref(py);
    let existing_defs = pb.definitions.clone_ref(py);
    drop(pb);

    let new_tds = PyList::empty_bound(py);
    let new_defs = PyList::empty_bound(py);

    // uninterpreted_lit = SVar(Name("uninterpreted", 0))
    let uninterp_name = mk_name(py, "uninterpreted", 0)?;
    let uninterp_lit = mk_svar(py, uninterp_name, default_loc(py))?;

    // Look up constructor_registry.register_constructors
    let registry_mod = py.import_bound("aeon.verification.constructor_registry")?;
    let register_fn = registry_mod.getattr("register_constructors")?;

    let ind_b = inductive_decls.bind(py);
    for i in 0..ind_b.len() {
        let indany = ind_b.get_item(i)?;
        let indpy = indany.downcast::<InductiveDecl>()?;
        let ind = indpy.borrow();
        let ind_name = ind.name.clone_ref(py);
        let ind_args = ind.args.clone_ref(py);
        let dtype_rfs = ind.rforalls.clone_ref(py);
        let constructors = ind.constructors.clone_ref(py);
        let measures = ind.measures.clone_ref(py);
        let ind_loc = ind.loc.clone_ref(py);
        drop(ind);

        // TypeDecl
        let td = Py::new(
            py,
            (
                TypeDecl {
                    name: ind_name.clone_ref(py),
                    args: ind_args.clone_ref(py),
                    loc: ind_loc.clone_ref(py),
                },
                Node,
            ),
        )?;
        new_tds.append(td)?;

        // Measures
        let meas_b = measures.bind(py);
        for j in 0..meas_b.len() {
            let m = meas_b.get_item(j)?;
            let md = m.downcast::<Definition>()?;
            let md = md.borrow();
            let merged_mr = merge_inductive_rforalls(py, &dtype_rfs, &md.rforalls.clone_ref(py))?;
            let de = Py::new(
                py,
                (
                    Definition {
                        name: md.name.clone_ref(py),
                        foralls: md.foralls.clone_ref(py),
                        args: md.args.clone_ref(py),
                        type_: md.type_.clone_ref(py),
                        body: uninterp_lit.clone_ref(py),
                        decorators: md.decorators.clone_ref(py),
                        rforalls: merged_mr,
                        decreasing_by: md.decreasing_by.clone_ref(py),
                        arg_multiplicities: md.arg_multiplicities.clone_ref(py),
                        loc: md.loc.clone_ref(py),
                    },
                    Node,
                ),
            )?;
            drop(md);
            new_defs.append(de)?;
        }

        // Helper: key_for
        let ind_name_str = name_str(py, &ind_name);
        let key_for = |cons_name: &Py<Name>| -> String {
            format!("{}_{}", ind_name_str, name_str(py, cons_name))
        };

        // Register constructor groups
        let groups_list = PyList::empty_bound(py);
        let cons_b = constructors.bind(py);
        for j in 0..cons_b.len() {
            let c = cons_b.get_item(j)?;
            let cd = c.downcast::<Definition>()?;
            let cd = cd.borrow();
            let cname = cd.name.clone_ref(py);
            drop(cd);
            groups_list.append(key_for(&cname))?;
        }
        register_fn.call1((ind_name_str.clone(), groups_list))?;

        // Emit constructor definitions
        let cons_b = constructors.bind(py);
        for j in 0..cons_b.len() {
            let c = cons_b.get_item(j)?;
            let cd = c.downcast::<Definition>()?;
            let cd = cd.borrow();
            let cname = cd.name.clone_ref(py);
            let cforalls = cd.foralls.clone_ref(py);
            let cargs = cd.args.clone_ref(py);
            let crtype = cd.type_.clone_ref(py);
            let cdecs = cd.decorators.clone_ref(py);
            let c_rf = cd.rforalls.clone_ref(py);
            let c_decr = cd.decreasing_by.clone_ref(py);
            let cloc = cd.loc.clone_ref(py);
            let cmults = cd.arg_multiplicities.clone_ref(py);
            drop(cd);

            // arg_s = ", ".join(str(arg.name) for (arg, _) in cargs)
            let ca_b = cargs.bind(py);
            let mut arg_parts: Vec<String> = Vec::with_capacity(ca_b.len());
            for k in 0..ca_b.len() {
                let pair = ca_b.get_item(k)?;
                let arg = pair.get_item(0)?;
                let an: Py<Name> = arg.downcast::<Name>()?.clone().unbind();
                arg_parts.push(an.borrow(py).__str__());
            }
            let arg_s = arg_parts.join(", ");
            let key = key_for(&cname);
            let lit_value: PyObject = PyString::new_bound(py, &format!("('{}', {})", key, arg_s)).into_any().unbind();
            let lit = Py::new(
                py,
                (SLiteral { value: lit_value, type_: st_string(py)?, loc: default_loc(py) }, STerm),
            )?
            .into_any();
            // native_var = SVar(Name("native", 0))
            let native_name = mk_name(py, "native", 0)?;
            let native_var = mk_svar(py, native_name, default_loc(py))?;
            let mk_tuple = mk_sapplication(py, native_var, lit, default_loc(py))?;

            let merged_cr = merge_inductive_rforalls(py, &dtype_rfs, &c_rf)?;
            let prefixed = mk_name(py, &format!("{}_{}", ind_name_str, name_str(py, &cname)), name_id(py, &cname))?;

            let de = Py::new(
                py,
                (
                    Definition {
                        name: prefixed,
                        foralls: cforalls,
                        args: cargs,
                        type_: crtype,
                        body: mk_tuple,
                        decorators: cdecs,
                        rforalls: merged_cr,
                        decreasing_by: c_decr,
                        arg_multiplicities: cmults,
                        loc: cloc,
                    },
                    Node,
                ),
            )?;
            new_defs.append(de)?;
        }

        // Generate the eliminator body as a Python expression chain
        // Mirror master:
        //   body = "case_<cname>" + "(this[i+1])"...
        //   guard = "this[0] == '<key>'"
        //   rec_expr = "(_ for _ in ()).throw(Exception('Invalid constructor'))"
        //   for body, guard in reversed(branches): rec_expr = f"({body} if {guard} else {rec_expr})"
        let mut branches_strs: Vec<(String, String)> = Vec::new();
        let cons_b = constructors.bind(py);
        for j in 0..cons_b.len() {
            let c = cons_b.get_item(j)?;
            let cd = c.downcast::<Definition>()?;
            let cd = cd.borrow();
            let cname = cd.name.clone_ref(py);
            let cargs = cd.args.clone_ref(py);
            drop(cd);
            let mut bdy = format!("case_{}", name_str(py, &cname));
            let ca_b = cargs.bind(py);
            for k in 0..ca_b.len() {
                bdy.push_str(&format!("(this[{}])", k + 1));
            }
            let key = key_for(&cname);
            let guard = format!("this[0] == '{}'", key);
            branches_strs.push((bdy, guard));
        }
        let mut rec_expr = String::from("(_ for _ in ()).throw(Exception('Invalid constructor'))");
        for (body, guard) in branches_strs.iter().rev() {
            rec_expr = format!("({} if {} else {})", body, guard, rec_expr);
        }
        let rec_lit_value: PyObject = PyString::new_bound(py, &rec_expr).into_any().unbind();
        let rec_lit = Py::new(
            py,
            (SLiteral { value: rec_lit_value, type_: st_string(py)?, loc: default_loc(py) }, STerm),
        )?
        .into_any();
        let native_name2 = mk_name(py, "native", 0)?;
        let native_var2 = mk_svar(py, native_name2, default_loc(py))?;
        let rec_body = mk_sapplication(py, native_var2, rec_lit, default_loc(py))?;

        // foralls: [(a, BaseKind()) for a in args]
        let bk = Py::new(py, (BaseKind, Kind))?;
        let foralls_list = PyList::empty_bound(py);
        let ia_b = ind_args.bind(py);
        for j in 0..ia_b.len() {
            let a: Py<Name> = ia_b.get_item(j)?.downcast::<Name>()?.clone().unbind();
            let tup = PyTuple::new_bound(py, &[a.into_any(), bk.clone_ref(py).into_any()]).unbind();
            foralls_list.append(tup)?;
        }

        // Return Type
        let return_generic_name = mk_name(py, "ret", -1)?;
        let return_type = mk_stypevar(py, return_generic_name.clone_ref(py), default_loc(py))?;
        let last_forall = PyTuple::new_bound(py, &[return_generic_name.into_any(), bk.clone_ref(py).into_any()]).unbind();
        foralls_list.append(last_forall)?;

        // Target Type = STypeConstructor(name, [STypeVar(a) for a in args])
        let ttargs = PyList::empty_bound(py);
        for j in 0..ia_b.len() {
            let a: Py<Name> = ia_b.get_item(j)?.downcast::<Name>()?.clone().unbind();
            let tv = mk_stypevar(py, a, default_loc(py))?;
            ttargs.append(tv)?;
        }
        let target_type = mk_stypeconstructor(py, ind_name.clone_ref(py), ttargs.unbind(), default_loc(py))?;

        let rec_args = PyList::empty_bound(py);
        let this_name = mk_name(py, "this", -1)?;
        let tup = PyTuple::new_bound(py, &[this_name.into_any(), target_type]).unbind();
        rec_args.append(tup)?;

        // For each constructor, add (Name(f"case_<name>", -1), curry(cargs, return_type, cmults))
        let cons_b = constructors.bind(py);
        for j in 0..cons_b.len() {
            let c = cons_b.get_item(j)?;
            let cd = c.downcast::<Definition>()?;
            let cd = cd.borrow();
            let cname = cd.name.clone_ref(py);
            let cargs = cd.args.clone_ref(py);
            let cmults = cd.arg_multiplicities.clone_ref(py);
            drop(cd);

            // Build curried type
            let mut rty = return_type.clone_ref(py);
            let ca_b = cargs.bind(py);
            let n = ca_b.len();
            let cmults_b = cmults.bind(py);
            let cmults_len: usize = cmults_b.len().unwrap_or(0);
            for k in 0..n {
                let idx = n - 1 - k;
                let pair = ca_b.get_item(idx)?;
                let aname: Py<Name> = pair.get_item(0)?.downcast::<Name>()?.clone().unbind();
                let aty: PyObject = pair.get_item(1)?.unbind();
                let m = if idx < cmults_len {
                    cmults_b.get_item(idx)?.unbind()
                } else {
                    crate::types::default_multiplicity(py)
                };
                rty = mk_sabstractiontype(py, aname, aty, rty, default_loc(py), m)?;
            }

            let case_name = mk_name(py, &format!("case_{}", name_str(py, &cname)), -1)?;
            let tup = PyTuple::new_bound(py, &[case_name.into_any(), rty]).unbind();
            rec_args.append(tup)?;
        }

        let rec_de = Py::new(
            py,
            (
                Definition {
                    name: mk_name(py, &format!("{}_rec", ind_name_str), -1)?,
                    foralls: foralls_list.unbind(),
                    args: rec_args.unbind(),
                    type_: return_type,
                    body: rec_body,
                    decorators: PyList::empty_bound(py).unbind(),
                    rforalls: {
                        // list(dtype_rfs)
                        let l = PyList::empty_bound(py);
                        let dt_b = dtype_rfs.bind(py);
                        for k in 0..dt_b.len() {
                            l.append(dt_b.get_item(k)?)?;
                        }
                        l.unbind()
                    },
                    decreasing_by: PyList::empty_bound(py).unbind(),
                    arg_multiplicities: PyTuple::empty_bound(py).into_any().unbind(),
                    loc: ind_loc,
                },
                Node,
            ),
        )?;
        new_defs.append(rec_de)?;
    }

    // Append existing defs
    let ed_b = existing_defs.bind(py);
    for i in 0..ed_b.len() {
        new_defs.append(ed_b.get_item(i)?)?;
    }
    // Append existing type_decls
    let combined_tds = PyList::empty_bound(py);
    let etd_b = existing_type_decls.bind(py);
    for i in 0..etd_b.len() {
        combined_tds.append(etd_b.get_item(i)?)?;
    }
    for i in 0..new_tds.len() {
        combined_tds.append(new_tds.get_item(i)?)?;
    }

    let new_p = Py::new(
        py,
        (
            Program {
                imports,
                type_decls: combined_tds.unbind(),
                inductive_decls: PyList::empty_bound(py).unbind(),
                definitions: new_defs.unbind(),
            },
            Node,
        ),
    )?;
    Ok(new_p)
}

// =============================================================================
// lower_match_to_inductive_rec
// =============================================================================

struct CtorInfo {
    iname: Py<Name>,
    cons_map: Vec<(Py<Name>, Py<PyList>)>, // (constructor_name, cargs list)
    constructor_order: Vec<(Py<Name>, Py<PyList>)>, // ordered list of (cname, cargs)
}

fn build_inductive_info(py: Python<'_>, inductive_decls: &Py<PyList>) -> PyResult<Vec<CtorInfo>> {
    let mut out = Vec::new();
    let il = inductive_decls.bind(py);
    for i in 0..il.len() {
        let ind = il.get_item(i)?;
        let ind = ind.downcast::<InductiveDecl>()?;
        let ind = ind.borrow();
        let iname = ind.name.clone_ref(py);
        let cons = ind.constructors.clone_ref(py);
        drop(ind);
        let mut cons_map: Vec<(Py<Name>, Py<PyList>)> = Vec::new();
        let mut order: Vec<(Py<Name>, Py<PyList>)> = Vec::new();
        let cl = cons.bind(py);
        for j in 0..cl.len() {
            let c = cl.get_item(j)?;
            let cd = c.downcast::<Definition>()?;
            let cd = cd.borrow();
            let cname = cd.name.clone_ref(py);
            let cargs = cd.args.clone_ref(py);
            drop(cd);
            cons_map.push((cname.clone_ref(py), cargs.clone_ref(py)));
            order.push((cname, cargs));
        }
        out.push(CtorInfo { iname, cons_map, constructor_order: order });
    }
    Ok(out)
}

fn lower_match_term(
    py: Python<'_>,
    t: PyObject,
    inductive_info: &[CtorInfo],
) -> PyResult<PyObject> {
    let b = t.bind(py);

    if let Ok(sm) = b.downcast::<SMatch>() {
        let sm = sm.borrow();
        let scrut = sm.scrutinee.clone_ref(py);
        let branches = sm.branches.clone_ref(py);
        let loc = sm.loc.clone_ref(py);
        drop(sm);

        let lowered_scrut = lower_match_term(py, scrut, inductive_info)?;

        // Collect (constructor name, qualifier) per branch
        let bs = branches.bind(py);
        let mut cons_names: Vec<Py<Name>> = Vec::with_capacity(bs.len());
        let mut quals: Vec<Option<String>> = Vec::with_capacity(bs.len());
        for i in 0..bs.len() {
            let br = bs.get_item(i)?;
            let br = br.downcast::<SMatchBranch>()?;
            let br = br.borrow();
            cons_names.push(br.constructor.clone_ref(py));
            quals.push(br.qualifier.clone());
        }

        // Find inductive: if any branch has qualifier, prefer that.
        let mut chosen: Option<usize> = None;
        for q in quals.iter() {
            if let Some(qstr) = q {
                for (idx, info) in inductive_info.iter().enumerate() {
                    if info.iname.borrow(py).name == *qstr {
                        chosen = Some(idx);
                        break;
                    }
                }
                break;
            }
        }
        if chosen.is_none() {
            // Find first inductive that contains all branch constructors
            for (idx, info) in inductive_info.iter().enumerate() {
                let mut all_match = true;
                for cn in cons_names.iter() {
                    let mut found = false;
                    for (k, _) in info.cons_map.iter() {
                        if pyname_eq(py, cn, k) {
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        all_match = false;
                        break;
                    }
                }
                if all_match {
                    chosen = Some(idx);
                    break;
                }
            }
        }

        if chosen.is_none() {
            // Build a new SMatch with lowered branches (only scrutinee is lowered here; preserve branches)
            // The Python version does: return SMatch(lowered_scrut, lowered_branches, loc=t.loc)
            // where lowered_branches = original `branches`. Preserve identity.
            return mk_smatch(py, lowered_scrut, branches, loc);
        }
        let info = &inductive_info[chosen.unwrap()];

        // rec_name = Name(<info.iname.name>_rec, -1)
        let ind_name_str = info.iname.borrow(py).name.clone();
        let rec_name = mk_name(py, &format!("{}_rec", ind_name_str), -1)?;
        let rec_fun = mk_svar(py, rec_name, loc.clone_ref(py))?;

        // Build handlers in constructor order
        let mut handlers: Vec<PyObject> = Vec::new();
        for (cname, cargs) in info.constructor_order.iter() {
            // find matching branch
            let mut found_body: Option<PyObject> = None;
            let mut found_binders: Option<Py<PyList>> = None;
            for i in 0..bs.len() {
                let br = bs.get_item(i)?;
                let br = br.downcast::<SMatchBranch>()?;
                let br = br.borrow();
                if pyname_eq(py, &br.constructor, cname) {
                    found_body = Some(br.body.clone_ref(py));
                    found_binders = Some(br.binders.clone_ref(py));
                    break;
                }
            }
            let (branch_expr, branch_binders): (PyObject, Py<PyList>) = match found_body {
                Some(body) => (body, found_binders.unwrap()),
                None => {
                    // Hole + cargs binder names as fallback
                    let hole_name = mk_name(py, "todo", -1)?;
                    let h = mk_shole(py, hole_name, loc.clone_ref(py))?;
                    let bl = PyList::empty_bound(py);
                    let ca_b = cargs.bind(py);
                    for k in 0..ca_b.len() {
                        let pair = ca_b.get_item(k)?;
                        let arg: Py<Name> = pair.get_item(0)?.downcast::<Name>()?.clone().unbind();
                        bl.append(arg)?;
                    }
                    (h, bl.unbind())
                }
            };

            // Use branch_binders if non-empty, else carg names.
            let binders_to_use: Py<PyList> = if branch_binders.bind(py).len() > 0 {
                branch_binders
            } else {
                let bl = PyList::empty_bound(py);
                let ca_b = cargs.bind(py);
                for k in 0..ca_b.len() {
                    let pair = ca_b.get_item(k)?;
                    let arg: Py<Name> = pair.get_item(0)?.downcast::<Name>()?.clone().unbind();
                    bl.append(arg)?;
                }
                bl.unbind()
            };

            let body = lower_match_term(py, branch_expr, inductive_info)?;
            // Wrap in abstractions: reversed binders
            let bl = binders_to_use.bind(py);
            let n = bl.len();
            let mut body_acc = body;
            for k in 0..n {
                let idx = n - 1 - k;
                let bn: Py<Name> = bl.get_item(idx)?.downcast::<Name>()?.clone().unbind();
                body_acc = mk_sabstraction(py, bn, body_acc, loc.clone_ref(py))?;
            }
            handlers.push(body_acc);
        }

        let mut out = mk_sapplication(py, rec_fun, lowered_scrut, loc.clone_ref(py))?;
        for h in handlers {
            out = mk_sapplication(py, out, h, loc.clone_ref(py))?;
        }
        return Ok(out);
    }

    if let Ok(sapp) = b.downcast::<SApplication>() {
        let sapp = sapp.borrow();
        let fun = sapp.fun.clone_ref(py);
        let arg = sapp.arg.clone_ref(py);
        let loc = sapp.loc.clone_ref(py);
        drop(sapp);
        return mk_sapplication(py, lower_match_term(py, fun, inductive_info)?, lower_match_term(py, arg, inductive_info)?, loc);
    }
    if let Ok(ab) = b.downcast::<SAbstraction>() {
        let ab = ab.borrow();
        let name = ab.var_name.clone_ref(py);
        let body = ab.body.clone_ref(py);
        let loc = ab.loc.clone_ref(py);
        drop(ab);
        return mk_sabstraction(py, name, lower_match_term(py, body, inductive_info)?, loc);
    }
    if let Ok(sl) = b.downcast::<SLet>() {
        let sl = sl.borrow();
        let name = sl.var_name.clone_ref(py);
        let v = sl.var_value.clone_ref(py);
        let bo = sl.body.clone_ref(py);
        let loc = sl.loc.clone_ref(py);
        let mult = sl.multiplicity.clone_ref(py);
        drop(sl);
        return mk_slet(py, name, lower_match_term(py, v, inductive_info)?, lower_match_term(py, bo, inductive_info)?, loc, mult);
    }
    if let Ok(sr) = b.downcast::<SRec>() {
        let sr = sr.borrow();
        let name = sr.var_name.clone_ref(py);
        let ty = sr.var_type.clone_ref(py);
        let v = sr.var_value.clone_ref(py);
        let bo = sr.body.clone_ref(py);
        let decr = sr.decreasing_by.clone_ref(py);
        let loc = sr.loc.clone_ref(py);
        let mult = sr.multiplicity.clone_ref(py);
        drop(sr);
        let decr_b = decr.bind(py);
        let mut new_decr: Vec<PyObject> = Vec::with_capacity(decr_b.len());
        for i in 0..decr_b.len() {
            new_decr.push(lower_match_term(py, decr_b.get_item(i)?.unbind(), inductive_info)?);
        }
        let new_decr_tuple = PyTuple::new_bound(py, new_decr).unbind();
        return mk_srec(py, name, ty, lower_match_term(py, v, inductive_info)?, lower_match_term(py, bo, inductive_info)?, new_decr_tuple, loc, mult);
    }
    if let Ok(si) = b.downcast::<SIf>() {
        let si = si.borrow();
        let cond = si.cond.clone_ref(py);
        let th = si.then.clone_ref(py);
        let el = si.otherwise.clone_ref(py);
        let loc = si.loc.clone_ref(py);
        drop(si);
        return mk_sif(py, lower_match_term(py, cond, inductive_info)?, lower_match_term(py, th, inductive_info)?, lower_match_term(py, el, inductive_info)?, loc);
    }
    if let Ok(sa) = b.downcast::<SAnnotation>() {
        let sa = sa.borrow();
        let e = sa.expr.clone_ref(py);
        let ty = sa.type_.clone_ref(py);
        let loc = sa.loc.clone_ref(py);
        drop(sa);
        return mk_sannotation(py, lower_match_term(py, e, inductive_info)?, ty, loc);
    }
    if let Ok(sta) = b.downcast::<STypeApplication>() {
        let sta = sta.borrow();
        let body = sta.body.clone_ref(py);
        let ty = sta.type_.clone_ref(py);
        let loc = sta.loc.clone_ref(py);
        drop(sta);
        return mk_stypeapplication(py, lower_match_term(py, body, inductive_info)?, ty, loc);
    }
    if let Ok(sta) = b.downcast::<STypeAbstraction>() {
        let sta = sta.borrow();
        let name = sta.name.clone_ref(py);
        let kind = sta.kind.clone_ref(py);
        let body = sta.body.clone_ref(py);
        let loc = sta.loc.clone_ref(py);
        drop(sta);
        return mk_stypeabstraction(py, name, kind, lower_match_term(py, body, inductive_info)?, loc);
    }
    if let Ok(sra) = b.downcast::<SRefinementApplication>() {
        let sra = sra.borrow();
        let body = sra.body.clone_ref(py);
        let refn = sra.refinement.clone_ref(py);
        let loc = sra.loc.clone_ref(py);
        drop(sra);
        return mk_srefinement_application(py, lower_match_term(py, body, inductive_info)?, lower_match_term(py, refn, inductive_info)?, loc);
    }
    if let Ok(sra) = b.downcast::<SRefinementAbstraction>() {
        let sra = sra.borrow();
        let name = sra.name.clone_ref(py);
        let sort = sra.sort.clone_ref(py);
        let body = sra.body.clone_ref(py);
        let loc = sra.loc.clone_ref(py);
        drop(sra);
        return mk_srefinement_abstraction(py, name, sort, lower_match_term(py, body, inductive_info)?, loc);
    }
    Ok(t)
}

#[pyfunction]
pub fn lower_match_to_inductive_rec(
    py: Python<'_>,
    prog: PyObject,
    inductive_decls: Py<PyList>,
) -> PyResult<PyObject> {
    let info = build_inductive_info(py, &inductive_decls)?;
    lower_match_term(py, prog, &info)
}

// Silence unused-import warnings for items pulled in only behind specific paths.
#[allow(dead_code)]
fn _force_use(_py: Python<'_>) {
    let _ = DesugarError::new_err("");
}
