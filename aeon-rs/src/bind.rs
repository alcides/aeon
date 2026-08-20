//! Name-resolution / binding pass for sugar AST.
//! Port of `aeon.sugar.bind`.
//!
//! Walks the sugar AST and assigns fresh `Name.id` values to every binding
//! occurrence whose id is currently `-1`. References get rewritten to point
//! to the most recent binder in scope.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};

use crate::elabctx::{
    ElabTypeDecl, ElabTypeVarBinder, ElabTypingContextEntry, ElabUninterpretedBinder,
    ElabVariableBinder, ElaborationTypingContext,
};
use crate::loc::default_location;
use crate::name::{next_fresh_id, Name};
use crate::sugar::{
    Decorator, Definition, InductiveDecl, Program, SAbstraction, SAbstractionType, SAnnotation,
    SAnonConstructor, SApplication, SBy, SHole, SIf, SLet, SLiteral, SMatch, SMatchBranch,
    SQualifiedVar, SRec, SRefinedType, SRefinementAbstraction, SRefinementApplication,
    SRefinementPolymorphism, STerm, STypeAbstraction, STypeApplication, STypeConstructor,
    STypePolymorphism, STypeVar, SType, SVar, TypeDecl,
};

/// RenamingSubstitions: an ordered list of `(name_str, fresh Py<Name>)`.
/// `Vec<(String, Py<Name>)>` is the natural Rust representation; the order
/// matters because we always pick the most recent binding (scan from the end).
pub type Subs = Vec<(String, Py<Name>)>;

pub fn clone_subs(py: Python<'_>, s: &Subs) -> Subs {
    s.iter().map(|(k, v)| (k.clone(), v.clone_ref(py))).collect()
}

fn name_str_id(py: Python<'_>, n: &Py<Name>) -> (String, i64) {
    let b = n.borrow(py);
    (b.name.clone(), b.id)
}

fn make_name(py: Python<'_>, n: &str, id: i64) -> PyResult<Py<Name>> {
    Py::new(py, Name { name: n.to_string(), id })
}

/// Returns the most recent fresh id assigned to the given source name.
fn get_last_id(py: Python<'_>, x: &str, subs: &Subs) -> Option<Py<Name>> {
    for (sub, v) in subs.iter().rev() {
        if sub == x {
            return Some(v.clone_ref(py));
        }
    }
    None
}

/// If `name.id == -1`, mint a fresh id and append `(name.name, fresh_name)`
/// to subs; otherwise pass it through unchanged (still appending so future
/// lookups can find it).
pub fn check_name(py: Python<'_>, name: Py<Name>, subs: &mut Subs) -> PyResult<Py<Name>> {
    let (nstr, nid) = name_str_id(py, &name);
    if nid == -1 {
        let new_id = next_fresh_id(py)?;
        let nname = make_name(py, &nstr, new_id)?;
        subs.push((nstr, nname.clone_ref(py)));
        Ok(nname)
    } else {
        subs.push((nstr, name.clone_ref(py)));
        Ok(name)
    }
}

/// Look up a name in subs by its `name` part; if found, return the bound
/// variant, else return the original.
pub fn apply_subs_name(py: Python<'_>, subs: &Subs, name: &Py<Name>) -> Py<Name> {
    let nstr = name.borrow(py).name.clone();
    for (sub, v) in subs.iter().rev() {
        if sub == &nstr {
            return v.clone_ref(py);
        }
    }
    name.clone_ref(py)
}

/// Bind an elaboration typing context — rename binder occurrences, recurse
/// into types.
fn bind_ectx(
    py: Python<'_>,
    ectx: &ElaborationTypingContext,
    subs: &mut Subs,
) -> PyResult<ElaborationTypingContext> {
    let entries = ectx.entries.bind(py);
    let new_entries = PyList::empty_bound(py);

    for i in 0..entries.len() {
        let entry = entries.get_item(i)?;

        if let Ok(vb) = entry.downcast::<ElabVariableBinder>() {
            let vb = vb.borrow();
            let nname = check_name(py, vb.name.clone_ref(py), subs)?;
            let nty = bind_stype(py, vb.type_.clone_ref(py), subs)?;
            let pe = Py::new(
                py,
                (
                    ElabVariableBinder { name: nname, type_: nty },
                    ElabTypingContextEntry,
                ),
            )?;
            new_entries.append(pe)?;
        } else if let Ok(ub) = entry.downcast::<ElabUninterpretedBinder>() {
            let ub = ub.borrow();
            let nname = check_name(py, ub.name.clone_ref(py), subs)?;
            let nty = bind_stype(py, ub.type_.clone_ref(py), subs)?;
            let pe = Py::new(
                py,
                (
                    ElabUninterpretedBinder { name: nname, type_: nty },
                    ElabTypingContextEntry,
                ),
            )?;
            new_entries.append(pe)?;
        } else if let Ok(tv) = entry.downcast::<ElabTypeVarBinder>() {
            let tv = tv.borrow();
            let nname = check_name(py, tv.name.clone_ref(py), subs)?;
            let kind = tv.type_.clone_ref(py);
            let pe = Py::new(
                py,
                (
                    ElabTypeVarBinder { name: nname, type_: kind },
                    ElabTypingContextEntry,
                ),
            )?;
            new_entries.append(pe)?;
        } else if let Ok(td) = entry.downcast::<ElabTypeDecl>() {
            let td = td.borrow();
            let nname = check_name(py, td.name.clone_ref(py), subs)?;
            let args = td.args.clone_ref(py);
            let pe = Py::new(
                py,
                (ElabTypeDecl { name: nname, args }, ElabTypingContextEntry),
            )?;
            new_entries.append(pe)?;
        } else {
            return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
                "{} not yet supported in bind.",
                entry.str()?
            )));
        }
    }

    Ok(ElaborationTypingContext {
        entries: new_entries.unbind(),
        constructor_to_type: ectx.constructor_to_type.clone_ref(py),
        constructor_defs: ectx.constructor_defs.clone_ref(py),
    })
}

fn bind_stype(py: Python<'_>, ty: PyObject, subs: &mut Subs) -> PyResult<PyObject> {
    let b = ty.bind(py);

    if let Ok(stv) = b.downcast::<STypeVar>() {
        let stv = stv.borrow();
        let nname = apply_subs_name(py, subs, &stv.name);
        let loc = stv.loc.clone_ref(py);
        drop(stv);
        return Ok(Py::new(
            py,
            (STypeVar { name: nname, loc }, SType),
        )?
        .into_any());
    }

    if let Ok(stc) = b.downcast::<STypeConstructor>() {
        let stc = stc.borrow();
        let new_args = PyList::empty_bound(py);
        let args = stc.args.bind(py);
        for i in 0..args.len() {
            let item = args.get_item(i)?.unbind();
            let nitem = bind_stype(py, item, subs)?;
            new_args.append(nitem)?;
        }
        let nname = apply_subs_name(py, subs, &stc.name);
        let loc = stc.loc.clone_ref(py);
        drop(stc);
        return Ok(Py::new(
            py,
            (
                STypeConstructor { name: nname, args: new_args.unbind(), loc },
                SType,
            ),
        )?
        .into_any());
    }

    if let Ok(sat) = b.downcast::<SAbstractionType>() {
        let sat = sat.borrow();
        let aname = sat.var_name.clone_ref(py);
        let atype = sat.var_type.clone_ref(py);
        let rtype = sat.type_.clone_ref(py);
        let loc = sat.loc.clone_ref(py);
        let mult = sat.multiplicity.clone_ref(py);
        drop(sat);

        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, aname, &mut nsubs)?;

        let new_atype = bind_stype(py, atype, subs)?;
        let new_rtype = bind_stype(py, rtype, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                SAbstractionType {
                    var_name: nname,
                    var_type: new_atype,
                    type_: new_rtype,
                    loc,
                    multiplicity: mult,
                },
                SType,
            ),
        )?
        .into_any());
    }

    if let Ok(srt) = b.downcast::<SRefinedType>() {
        let srt = srt.borrow();
        let name = srt.name.clone_ref(py);
        let ity = srt.type_.clone_ref(py);
        let refn = srt.refinement.clone_ref(py);
        let loc = srt.loc.clone_ref(py);
        drop(srt);
        let nty = bind_stype(py, ity, subs)?;
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nref = bind_sterm(py, refn, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                SRefinedType { name: nname, type_: nty, refinement: nref, loc },
                SType,
            ),
        )?
        .into_any());
    }

    if let Ok(stp) = b.downcast::<STypePolymorphism>() {
        let stp = stp.borrow();
        let name = stp.name.clone_ref(py);
        let kind = stp.kind.clone_ref(py);
        let body = stp.body.clone_ref(py);
        let loc = stp.loc.clone_ref(py);
        drop(stp);
        let nname = check_name(py, name, subs)?;
        let nbody = bind_stype(py, body, subs)?;
        return Ok(Py::new(
            py,
            (
                STypePolymorphism { name: nname, kind, body: nbody, loc },
                SType,
            ),
        )?
        .into_any());
    }

    if let Ok(srp) = b.downcast::<SRefinementPolymorphism>() {
        let srp = srp.borrow();
        let name = srp.name.clone_ref(py);
        let sort = srp.sort.clone_ref(py);
        let body = srp.body.clone_ref(py);
        let loc = srp.loc.clone_ref(py);
        drop(srp);
        let bound_sort = bind_stype(py, sort, subs)?;
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nbody = bind_stype(py, body, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                SRefinementPolymorphism { name: nname, sort: bound_sort, body: nbody, loc },
                SType,
            ),
        )?
        .into_any());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unique not supported for {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

fn bind_sterm(py: Python<'_>, t: PyObject, subs: &mut Subs) -> PyResult<PyObject> {
    let b = t.bind(py);

    if b.downcast::<SLiteral>().is_ok()
        || b.downcast::<SQualifiedVar>().is_ok()
        || b.downcast::<SAnonConstructor>().is_ok()
    {
        return Ok(t);
    }

    if let Ok(sv) = b.downcast::<SVar>() {
        let sv = sv.borrow();
        let nname = apply_subs_name(py, subs, &sv.name);
        let loc = sv.loc.clone_ref(py);
        drop(sv);
        return Ok(Py::new(py, (SVar { name: nname, loc }, STerm))?.into_any());
    }

    if let Ok(sh) = b.downcast::<SHole>() {
        let sh = sh.borrow();
        let name = sh.name.clone_ref(py);
        let loc = sh.loc.clone_ref(py);
        drop(sh);
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        return Ok(Py::new(py, (SHole { name: nname, loc }, STerm))?.into_any());
    }

    if let Ok(sby) = b.downcast::<SBy>() {
        let sby = sby.borrow();
        let steps = sby.steps.clone_ref(py);
        let loc = sby.loc.clone_ref(py);
        drop(sby);
        return Ok(Py::new(py, (SBy { steps, loc }, STerm))?.into_any());
    }

    if let Ok(sa) = b.downcast::<SAnnotation>() {
        let sa = sa.borrow();
        let expr = sa.expr.clone_ref(py);
        let ty = sa.type_.clone_ref(py);
        let loc = sa.loc.clone_ref(py);
        drop(sa);
        let nexpr = bind_sterm(py, expr, subs)?;
        let nty = bind_stype(py, ty, subs)?;
        return Ok(Py::new(py, (SAnnotation { expr: nexpr, type_: nty, loc }, STerm))?.into_any());
    }

    if let Ok(sap) = b.downcast::<SApplication>() {
        let sap = sap.borrow();
        let fun = sap.fun.clone_ref(py);
        let arg = sap.arg.clone_ref(py);
        let loc = sap.loc.clone_ref(py);
        drop(sap);
        let nfun = bind_sterm(py, fun, subs)?;
        let narg = bind_sterm(py, arg, subs)?;
        return Ok(Py::new(py, (SApplication { fun: nfun, arg: narg, loc }, STerm))?.into_any());
    }

    if let Ok(sab) = b.downcast::<SAbstraction>() {
        let sab = sab.borrow();
        let name = sab.var_name.clone_ref(py);
        let body = sab.body.clone_ref(py);
        let loc = sab.loc.clone_ref(py);
        drop(sab);
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nbody = bind_sterm(py, body, &mut nsubs)?;
        return Ok(Py::new(py, (SAbstraction { var_name: nname, body: nbody, loc }, STerm))?
            .into_any());
    }

    if let Ok(sta) = b.downcast::<STypeApplication>() {
        let sta = sta.borrow();
        let body = sta.body.clone_ref(py);
        let ty = sta.type_.clone_ref(py);
        let loc = sta.loc.clone_ref(py);
        drop(sta);
        let nbody = bind_sterm(py, body, subs)?;
        let nty = bind_stype(py, ty, subs)?;
        return Ok(Py::new(py, (STypeApplication { body: nbody, type_: nty, loc }, STerm))?
            .into_any());
    }

    if let Ok(sra) = b.downcast::<SRefinementApplication>() {
        let sra = sra.borrow();
        let body = sra.body.clone_ref(py);
        let refn = sra.refinement.clone_ref(py);
        let loc = sra.loc.clone_ref(py);
        drop(sra);
        let nbody = bind_sterm(py, body, subs)?;
        let nref = bind_sterm(py, refn, subs)?;
        return Ok(Py::new(
            py,
            (SRefinementApplication { body: nbody, refinement: nref, loc }, STerm),
        )?
        .into_any());
    }

    if let Ok(sta) = b.downcast::<STypeAbstraction>() {
        let sta = sta.borrow();
        let name = sta.name.clone_ref(py);
        let kind = sta.kind.clone_ref(py);
        let body = sta.body.clone_ref(py);
        let loc = sta.loc.clone_ref(py);
        drop(sta);
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nbody = bind_sterm(py, body, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (STypeAbstraction { name: nname, kind, body: nbody, loc }, STerm),
        )?
        .into_any());
    }

    if let Ok(sra) = b.downcast::<SRefinementAbstraction>() {
        let sra = sra.borrow();
        let name = sra.name.clone_ref(py);
        let sort = sra.sort.clone_ref(py);
        let body = sra.body.clone_ref(py);
        let loc = sra.loc.clone_ref(py);
        drop(sra);
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let nsort = bind_stype(py, sort, &mut nsubs)?;
        let nbody = bind_sterm(py, body, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                SRefinementAbstraction { name: nname, sort: nsort, body: nbody, loc },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sif) = b.downcast::<SIf>() {
        let sif = sif.borrow();
        let cond = sif.cond.clone_ref(py);
        let then = sif.then.clone_ref(py);
        let otherwise = sif.otherwise.clone_ref(py);
        let loc = sif.loc.clone_ref(py);
        drop(sif);
        let ncond = bind_sterm(py, cond, subs)?;
        let nthen = bind_sterm(py, then, subs)?;
        let nelse = bind_sterm(py, otherwise, subs)?;
        return Ok(Py::new(
            py,
            (
                SIf { cond: ncond, then: nthen, otherwise: nelse, loc },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sm) = b.downcast::<SMatch>() {
        let sm = sm.borrow();
        let scrutinee = sm.scrutinee.clone_ref(py);
        let branches = sm.branches.clone_ref(py);
        let loc = sm.loc.clone_ref(py);
        drop(sm);
        let nscrut = bind_sterm(py, scrutinee, subs)?;
        let brs = branches.bind(py);
        let new_branches = PyList::empty_bound(py);
        for i in 0..brs.len() {
            let br = brs.get_item(i)?;
            let mb = br.downcast::<SMatchBranch>()?;
            let mb = mb.borrow();
            let mut branch_subs: Subs = clone_subs(py, subs);
            // Pattern binders: each gets a fresh id (if -1) or passes through.
            let binders = mb.binders.bind(py);
            let renamed_binders = PyList::empty_bound(py);
            for j in 0..binders.len() {
                let bnd = binders.get_item(j)?;
                let bnd_name: Py<Name> = bnd.downcast::<Name>()?.clone().unbind();
                let nb = check_name(py, bnd_name, &mut branch_subs)?;
                renamed_binders.append(nb)?;
            }
            let body = mb.body.clone_ref(py);
            let qualifier = mb.qualifier.clone();
            let br_loc = mb.loc.clone_ref(py);
            // Align pattern constructor names with bound names.
            let ctor = apply_subs_name(py, subs, &mb.constructor);
            drop(mb);
            let nbody = bind_sterm(py, body, &mut branch_subs)?;
            let new_branch = Py::new(
                py,
                SMatchBranch {
                    constructor: ctor,
                    binders: renamed_binders.unbind(),
                    body: nbody,
                    qualifier,
                    loc: br_loc,
                },
            )?;
            new_branches.append(new_branch)?;
        }
        return Ok(Py::new(
            py,
            (
                SMatch { scrutinee: nscrut, branches: new_branches.unbind(), loc },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sl) = b.downcast::<SLet>() {
        let sl = sl.borrow();
        let name = sl.var_name.clone_ref(py);
        let body = sl.var_value.clone_ref(py);
        let cont = sl.body.clone_ref(py);
        let loc = sl.loc.clone_ref(py);
        let mult = sl.multiplicity.clone_ref(py);
        drop(sl);
        let nval = bind_sterm(py, body, subs)?;
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        let ncont = bind_sterm(py, cont, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                SLet { var_name: nname, var_value: nval, body: ncont, loc, multiplicity: mult },
                STerm,
            ),
        )?
        .into_any());
    }

    if let Ok(sr) = b.downcast::<SRec>() {
        let sr = sr.borrow();
        let name = sr.var_name.clone_ref(py);
        let ty = sr.var_type.clone_ref(py);
        let body = sr.var_value.clone_ref(py);
        let cont = sr.body.clone_ref(py);
        let decr = sr.decreasing_by.clone_ref(py);
        let loc = sr.loc.clone_ref(py);
        let mult = sr.multiplicity.clone_ref(py);
        drop(sr);
        let mut nsubs = clone_subs(py, subs);
        let nname = check_name(py, name, &mut nsubs)?;
        // Bind decreasing measures with the recursive name in scope.
        let decr_b = decr.bind(py);
        let mut new_decr_vec: Vec<PyObject> = Vec::with_capacity(decr_b.len());
        for i in 0..decr_b.len() {
            let item = decr_b.get_item(i)?.unbind();
            let ni = bind_sterm(py, item, &mut nsubs)?;
            new_decr_vec.push(ni);
        }
        let new_decr = PyTuple::new_bound(py, new_decr_vec).unbind();
        let nty = bind_stype(py, ty, &mut nsubs)?;
        let nval = bind_sterm(py, body, &mut nsubs)?;
        let ncont = bind_sterm(py, cont, &mut nsubs)?;
        return Ok(Py::new(
            py,
            (
                SRec {
                    var_name: nname,
                    var_type: nty,
                    var_value: nval,
                    body: ncont,
                    decreasing_by: new_decr,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unique not supported for {} ({})",
        b.str()?,
        b.get_type().name()?
    )))
}

fn bind_definition(
    py: Python<'_>,
    df: &Definition,
    nsubs: &mut Subs,
) -> PyResult<Py<Definition>> {
    let name_ref = df.name.clone_ref(py);
    let new_name = check_name(py, name_ref, nsubs)?;

    // foralls: list[(Name, Kind)]
    let foralls_b = df.foralls.bind(py);
    let new_foralls = PyList::empty_bound(py);
    for i in 0..foralls_b.len() {
        let tup = foralls_b.get_item(i)?;
        let fname: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
        let kind = tup.get_item(1)?.unbind();
        let nname = check_name(py, fname, nsubs)?;
        let new_t = PyTuple::new_bound(py, &[nname.into_any(), kind]).unbind();
        new_foralls.append(new_t)?;
    }

    // args: list[(Name, SType)]
    let args_b = df.args.bind(py);
    let new_args = PyList::empty_bound(py);
    for i in 0..args_b.len() {
        let tup = args_b.get_item(i)?;
        let aname: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
        let aty = tup.get_item(1)?.unbind();
        let nname = check_name(py, aname, nsubs)?;
        let nty = bind_stype(py, aty, nsubs)?;
        let new_t = PyTuple::new_bound(py, &[nname.into_any(), nty]).unbind();
        new_args.append(new_t)?;
    }

    // rforalls: list[(Name, SType)]
    let rforalls_b = df.rforalls.bind(py);
    let new_rforalls = PyList::empty_bound(py);
    for i in 0..rforalls_b.len() {
        let tup = rforalls_b.get_item(i)?;
        let pname: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
        let psort = tup.get_item(1)?.unbind();
        let nname = check_name(py, pname, nsubs)?;
        let nsort = bind_stype(py, psort, nsubs)?;
        let new_t = PyTuple::new_bound(py, &[nname.into_any(), nsort]).unbind();
        new_rforalls.append(new_t)?;
    }

    let ntype = bind_stype(py, df.type_.clone_ref(py), nsubs)?;

    // decreasing_by: list[STerm]
    let decr_b = df.decreasing_by.bind(py);
    let new_decr = PyList::empty_bound(py);
    for i in 0..decr_b.len() {
        let m = decr_b.get_item(i)?.unbind();
        let nm = bind_sterm(py, m, nsubs)?;
        new_decr.append(nm)?;
    }

    let body = bind_sterm(py, df.body.clone_ref(py), nsubs)?;

    // decorators: list[Decorator]
    let dec_b = df.decorators.bind(py);
    let new_decorators = PyList::empty_bound(py);
    for i in 0..dec_b.len() {
        let dec = dec_b.get_item(i)?;
        let dec = dec.downcast::<Decorator>()?;
        let dec = dec.borrow();
        let dargs_b = dec.macro_args.bind(py);
        let new_dargs = PyList::empty_bound(py);
        for j in 0..dargs_b.len() {
            let it = dargs_b.get_item(j)?.unbind();
            let nit = bind_sterm(py, it, nsubs)?;
            new_dargs.append(nit)?;
        }
        // named_args: dict[Name, STerm]
        let na_obj = dec.named_args.clone_ref(py);
        let new_na = PyDict::new_bound(py);
        if let Ok(na) = na_obj.downcast_bound::<PyDict>(py) {
            for (k, v) in na.iter() {
                let nv = bind_sterm(py, v.unbind(), nsubs)?;
                new_na.set_item(k, nv)?;
            }
        }
        let name = dec.name.clone_ref(py);
        let loc = dec.loc.clone_ref(py);
        drop(dec);
        let nd = Py::new(
            py,
            (
                Decorator {
                    name,
                    macro_args: new_dargs.unbind(),
                    named_args: new_na.unbind().into_any(),
                    loc,
                },
                crate::sugar::Node,
            ),
        )?;
        new_decorators.append(nd)?;
    }

    let new_def = Py::new(
        py,
        (
            Definition {
                name: new_name,
                foralls: new_foralls.unbind(),
                args: new_args.unbind(),
                type_: ntype,
                body,
                decorators: new_decorators.unbind(),
                rforalls: new_rforalls.unbind(),
                decreasing_by: new_decr.unbind(),
                arg_multiplicities: df.arg_multiplicities.clone_ref(py),
                loc: df.loc.clone_ref(py),
            },
            crate::sugar::Node,
        ),
    )?;
    Ok(new_def)
}

#[pyfunction]
#[pyo3(signature = (p, subs = None))]
pub fn bind_program(
    py: Python<'_>,
    p: Py<Program>,
    subs: Option<Vec<(String, Py<Name>)>>,
) -> PyResult<Py<Program>> {
    let p_b = p.borrow(py);
    let initial: Subs = subs.unwrap_or_default();
    let mut nsubs: Subs = initial;

    let new_type_decls = PyList::empty_bound(py);
    let new_inductive_decls = PyList::empty_bound(py);
    let new_definitions = PyList::empty_bound(py);

    // Type decls first.
    let td_b = p_b.type_decls.bind(py);
    for i in 0..td_b.len() {
        let td = td_b.get_item(i)?;
        let td = td.downcast::<TypeDecl>()?;
        let td = td.borrow();
        let name = td.name.clone_ref(py);
        let nname = check_name(py, name, &mut nsubs)?;
        let args = td.args.clone_ref(py);
        let loc = td.loc.clone_ref(py);
        drop(td);
        let new_td = Py::new(
            py,
            (
                TypeDecl { name: nname, args, loc },
                crate::sugar::Node,
            ),
        )?;
        new_type_decls.append(new_td)?;
    }

    // Inductive decls.
    let ind_b = p_b.inductive_decls.bind(py);
    for i in 0..ind_b.len() {
        let ind = ind_b.get_item(i)?;
        let ind = ind.downcast::<InductiveDecl>()?;
        let ind = ind.borrow();
        let name = ind.name.clone_ref(py);
        let nname = check_name(py, name, &mut nsubs)?;

        let iargs_b = ind.args.bind(py);
        let new_iargs = PyList::empty_bound(py);
        for j in 0..iargs_b.len() {
            let aname: Py<Name> = iargs_b.get_item(j)?.downcast::<Name>()?.clone().unbind();
            let na = check_name(py, aname, &mut nsubs)?;
            new_iargs.append(na)?;
        }

        let rf_b = ind.rforalls.bind(py);
        let new_drfs = PyList::empty_bound(py);
        for j in 0..rf_b.len() {
            let tup = rf_b.get_item(j)?;
            let pname: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let psort = tup.get_item(1)?.unbind();
            let nname2 = check_name(py, pname, &mut nsubs)?;
            let nsort = bind_stype(py, psort, &mut nsubs)?;
            let new_t = PyTuple::new_bound(py, &[nname2.into_any(), nsort]).unbind();
            new_drfs.append(new_t)?;
        }

        let cons_b = ind.constructors.bind(py);
        let new_cons = PyList::empty_bound(py);
        for j in 0..cons_b.len() {
            let c = cons_b.get_item(j)?;
            let c = c.downcast::<Definition>()?;
            let c = c.borrow();
            let nc = bind_definition(py, &c, &mut nsubs)?;
            drop(c);
            new_cons.append(nc)?;
        }

        let meas_b = ind.measures.bind(py);
        let new_meas = PyList::empty_bound(py);
        for j in 0..meas_b.len() {
            let m = meas_b.get_item(j)?;
            let m = m.downcast::<Definition>()?;
            let m = m.borrow();
            let nm = bind_definition(py, &m, &mut nsubs)?;
            drop(m);
            new_meas.append(nm)?;
        }

        let loc = ind.loc.clone_ref(py);
        drop(ind);
        let new_ind = Py::new(
            py,
            (
                InductiveDecl {
                    name: nname,
                    args: new_iargs.unbind(),
                    rforalls: new_drfs.unbind(),
                    constructors: new_cons.unbind(),
                    measures: new_meas.unbind(),
                    loc,
                },
                crate::sugar::Node,
            ),
        )?;
        new_inductive_decls.append(new_ind)?;
    }

    // Definitions.
    let defs_b = p_b.definitions.bind(py);
    for i in 0..defs_b.len() {
        let d = defs_b.get_item(i)?;
        let d = d.downcast::<Definition>()?;
        let d = d.borrow();
        let nd = bind_definition(py, &d, &mut nsubs)?;
        drop(d);
        new_definitions.append(nd)?;
    }

    let imports = p_b.imports.clone_ref(py);
    drop(p_b);
    let new_program = Py::new(
        py,
        (
            Program {
                imports,
                type_decls: new_type_decls.unbind(),
                inductive_decls: new_inductive_decls.unbind(),
                definitions: new_definitions.unbind(),
            },
            crate::sugar::Node,
        ),
    )?;
    Ok(new_program)
}

#[pyfunction]
pub fn bind(
    py: Python<'_>,
    ectx: &ElaborationTypingContext,
    s: PyObject,
) -> PyResult<(ElaborationTypingContext, PyObject)> {
    let mut subs: Subs = Vec::new();
    let new_ectx = bind_ectx(py, ectx, &mut subs)?;
    let new_term = bind_sterm(py, s, &mut subs)?;
    Ok((new_ectx, new_term))
}

// Expose the low-level helpers too — keep Python tests' surface intact.
#[pyfunction]
pub fn py_bind_sterm(
    py: Python<'_>,
    t: PyObject,
    subs: Vec<(String, Py<Name>)>,
) -> PyResult<PyObject> {
    let mut subs = subs;
    bind_sterm(py, t, &mut subs)
}

#[pyfunction]
pub fn py_bind_ectx(
    py: Python<'_>,
    ectx: &ElaborationTypingContext,
    subs: Vec<(String, Py<Name>)>,
) -> PyResult<(ElaborationTypingContext, Vec<(String, Py<Name>)>)> {
    let mut subs = subs;
    let new_ectx = bind_ectx(py, ectx, &mut subs)?;
    Ok((new_ectx, subs))
}

#[pyfunction]
pub fn py_bind_stype(
    py: Python<'_>,
    ty: PyObject,
    subs: Vec<(String, Py<Name>)>,
) -> PyResult<PyObject> {
    let mut subs = subs;
    bind_stype(py, ty, &mut subs)
}

// Silence unused — needed for trait imports we depend on.
#[allow(dead_code)]
fn _force_use(py: Python<'_>) {
    let _ = default_location(py);
}
