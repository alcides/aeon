//! Sugar → Core lowering pass.
//! Port of `aeon.sugar.lowering`.

use pyo3::prelude::*;
use pyo3::types::PyList;

use crate::elabctx::{
    ElabTypeDecl, ElabTypeVarBinder, ElabUninterpretedBinder, ElabVariableBinder,
    ElaborationTypingContext,
};
use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidTerm, LiquidVar,
};
use crate::name::{next_fresh_id, Name};
use crate::sugar::{
    SAbstraction, SAbstractionType, SAnnotation, SApplication, SHole, SIf, SLet, SLiteral, SRec,
    SRefinedType, SRefinementAbstraction, SRefinementApplication, SRefinementPolymorphism, STerm,
    STypeAbstraction, STypeApplication, STypeConstructor, STypePolymorphism, STypeVar, SType,
    SVar,
};
use crate::sugar_helpers::{normalize, substitution_sterm_in_sterm, substitution_sterm_in_stype};
use crate::substitutions::{substitute_vartype, substitution_in_liquid};
use crate::terms::{
    Abstraction, Annotation, Application, Hole, If, Let, Literal, Rec, RefinementAbstraction,
    RefinementApplication, Term, TypeAbstraction, TypeApplication, Var,
};
use crate::typectx::{
    TypeBinder, TypeConstructorBinder, TypingContext, TypingContextEntry, UninterpretedBinder,
    VariableBinder,
};
use crate::types::{
    default_multiplicity, AbstractionType, RefinedType, RefinementPolymorphism, Top, Type,
    TypeConstructor, TypePolymorphism, TypeVar,
};

create_exception!(aeon_rs, LoweringException, pyo3::exceptions::PyException);
create_exception!(aeon_rs, LiquefactionException, LoweringException);

use pyo3::create_exception;

// Construct fresh t_unit / t_int on demand. The originals are Python module
// singletons (`aeon.core.types.t_unit`/`t_int`). Mirroring them as freshly
// constructed values is fine — equality is by name+id.
fn t_unit(py: Python<'_>) -> PyResult<PyObject> {
    let name = Py::new(py, Name { name: "Unit".to_string(), id: 0 })?;
    let tc = Py::new(
        py,
        (
            TypeConstructor { name, args: PyList::empty_bound(py).unbind(), loc: crate::loc::default_location(py) },
            Type,
        ),
    )?;
    Ok(tc.into_any())
}

fn t_int(py: Python<'_>) -> PyResult<PyObject> {
    let name = Py::new(py, Name { name: "Int".to_string(), id: 0 })?;
    let tc = Py::new(
        py,
        (
            TypeConstructor { name, args: PyList::empty_bound(py).unbind(), loc: crate::loc::default_location(py) },
            Type,
        ),
    )?;
    Ok(tc.into_any())
}

/// liquefy_app helper. Returns None on non-liquefiable inputs (mirrors the
/// Python None-or-LiquidApp/LiquidHornApplication return).
fn liquefy_app(
    py: Python<'_>,
    app: PyObject,
    available_vars: &Option<Py<PyList>>,
) -> PyResult<Option<PyObject>> {
    let app_b = app.bind(py);
    let app_obj = app_b.downcast::<SApplication>()?;
    let app_obj = app_obj.borrow();
    let arg_obj = app_obj.arg.clone_ref(py);
    let app_loc = app_obj.loc.clone_ref(py);
    let mut fun_obj = app_obj.fun.clone_ref(py);
    drop(app_obj);

    // Strip STypeApplication wrappers.
    loop {
        let fb = fun_obj.bind(py);
        if let Ok(sta) = fb.downcast::<STypeApplication>() {
            let sta = sta.borrow();
            let inner = sta.body.clone_ref(py);
            drop(sta);
            fun_obj = inner;
        } else {
            break;
        }
    }

    let av_for_arg = available_vars.as_ref().map(|v| v.clone_ref(py));
    let arg = liquefy(py, arg_obj, av_for_arg)?;
    let arg = match arg {
        Some(a) => a,
        None => return Ok(None),
    };

    let fb = fun_obj.bind(py);

    if let Ok(sv) = fb.downcast::<SVar>() {
        let sv = sv.borrow();
        let name = sv.name.clone_ref(py);
        drop(sv);
        let args = PyList::empty_bound(py);
        args.append(arg)?;
        let la = Py::new(
            py,
            (LiquidApp { fun: name, args: args.unbind(), loc: app_loc }, LiquidTerm),
        )?;
        return Ok(Some(la.into_any()));
    }
    if let Ok(sh) = fb.downcast::<SHole>() {
        let sh = sh.borrow();
        let name = sh.name.clone_ref(py);
        let loc = sh.loc.clone_ref(py);
        drop(sh);
        let argtypes = PyList::empty_bound(py);
        if let Some(av) = available_vars.as_ref() {
            let av_b = av.bind(py);
            for i in 0..av_b.len() {
                let tup = av_b.get_item(i)?;
                let xname: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
                let xty = tup.get_item(1)?.unbind();
                let lv = Py::new(py, (LiquidVar { name: xname, loc: crate::loc::default_location(py) }, LiquidTerm))?;
                let t2 = pyo3::types::PyTuple::new_bound(py, &[lv.into_any(), xty]).unbind();
                argtypes.append(t2)?;
            }
        }
        let lha = Py::new(
            py,
            (LiquidHornApplication { name, argtypes: argtypes.unbind(), loc }, LiquidTerm),
        )?;
        return Ok(Some(lha.into_any()));
    }
    if fb.downcast::<SApplication>().is_ok() {
        let liquid_pseudo = liquefy_app(py, fun_obj.clone_ref(py), available_vars)?;
        if let Some(lp) = liquid_pseudo {
            if let Ok(la) = lp.bind(py).downcast::<LiquidApp>() {
                let la = la.borrow();
                let fun = la.fun.clone_ref(py);
                let new_args = PyList::empty_bound(py);
                let oargs = la.args.bind(py);
                for i in 0..oargs.len() {
                    new_args.append(oargs.get_item(i)?)?;
                }
                new_args.append(arg)?;
                drop(la);
                let res = Py::new(
                    py,
                    (LiquidApp { fun, args: new_args.unbind(), loc: app_loc }, LiquidTerm),
                )?;
                return Ok(Some(res.into_any()));
            }
        }
        return Ok(None);
    }
    if let Ok(sl) = fb.downcast::<SLet>() {
        let sl = sl.borrow();
        let name = sl.var_name.clone_ref(py);
        let val = sl.var_value.clone_ref(py);
        let body = sl.body.clone_ref(py);
        drop(sl);
        let new_body = substitution_sterm_in_sterm(py, body, val, name)?;
        let arg_again = arg_obj_from(py, &app)?;
        let new_app = Py::new(
            py,
            (SApplication { fun: new_body, arg: arg_again, loc: app_loc }, STerm),
        )?
        .into_any();
        return liquefy_app(py, new_app, available_vars);
    }
    Err(LiquefactionException::new_err(format!(
        "{} is not a valid predicate.",
        app.bind(py).str()?
    )))
}

fn arg_obj_from(py: Python<'_>, app: &PyObject) -> PyResult<PyObject> {
    let a = app.bind(py).downcast::<SApplication>()?;
    Ok(a.borrow().arg.clone_ref(py))
}

/// Converts surface terms into liquid terms. Returns None if the term is
/// not liquefiable (mirrors Python's `None` returns).
#[pyfunction(name = "sugar_liquefy")]
#[pyo3(signature = (t, available_vars = None))]
pub fn liquefy(
    py: Python<'_>,
    t: PyObject,
    available_vars: Option<Py<PyList>>,
) -> PyResult<Option<PyObject>> {
    let b = t.bind(py);

    if let Ok(slit) = b.downcast::<SLiteral>() {
        let slit = slit.borrow();
        let value = slit.value.clone_ref(py);
        let ty = slit.type_.clone_ref(py);
        let loc = slit.loc.clone_ref(py);
        drop(slit);

        // Identify the constructor name.
        let ty_b = ty.bind(py);
        if let Ok(stc) = ty_b.downcast::<STypeConstructor>() {
            let stc = stc.borrow();
            let tname = stc.name.borrow(py).name.clone();
            drop(stc);
            match tname.as_str() {
                "Bool" => {
                    let v: bool = value.extract(py)?;
                    let lit = Py::new(py, (LiquidLiteralBool { value: v, loc }, LiquidTerm))?;
                    return Ok(Some(lit.into_any()));
                }
                "Int" => {
                    let v: i64 = value.extract(py)?;
                    let lit = Py::new(py, (LiquidLiteralInt { value: v, loc }, LiquidTerm))?;
                    return Ok(Some(lit.into_any()));
                }
                "Float" => {
                    let v: f64 = value.extract(py)?;
                    let lit = Py::new(py, (LiquidLiteralFloat { value: v, loc }, LiquidTerm))?;
                    return Ok(Some(lit.into_any()));
                }
                "String" => {
                    let v: String = value.extract(py)?;
                    let lit = Py::new(py, (LiquidLiteralString { value: v, loc }, LiquidTerm))?;
                    return Ok(Some(lit.into_any()));
                }
                _ => {}
            }
        }
        return Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "{} is not convertable to liquid term.",
            t.bind(py).str()?
        )));
    }

    if let Ok(sv) = b.downcast::<SVar>() {
        let sv = sv.borrow();
        let name = sv.name.clone_ref(py);
        let loc = sv.loc.clone_ref(py);
        drop(sv);
        return Ok(Some(
            Py::new(py, (LiquidVar { name, loc }, LiquidTerm))?.into_any(),
        ));
    }

    if let Ok(sif) = b.downcast::<SIf>() {
        let sif = sif.borrow();
        let cond = sif.cond.clone_ref(py);
        let then = sif.then.clone_ref(py);
        let otherwise = sif.otherwise.clone_ref(py);
        let loc = sif.loc.clone_ref(py);
        drop(sif);
        let av1 = available_vars.as_ref().map(|v| v.clone_ref(py));
        let av2 = available_vars.as_ref().map(|v| v.clone_ref(py));
        let co = liquefy(py, cond, av1)?;
        let th = liquefy(py, then, av2)?;
        let ot = liquefy(py, otherwise, available_vars)?;
        if let (Some(co), Some(th), Some(ot)) = (co, th, ot) {
            let args = PyList::empty_bound(py);
            args.append(co)?;
            args.append(th)?;
            args.append(ot)?;
            let ite_name = Py::new(py, Name { name: "ite".to_string(), id: 0 })?;
            let la = Py::new(
                py,
                (LiquidApp { fun: ite_name, args: args.unbind(), loc }, LiquidTerm),
            )?;
            return Ok(Some(la.into_any()));
        }
        return Ok(None);
    }

    if let Ok(sa) = b.downcast::<SAnnotation>() {
        let expr = sa.borrow().expr.clone_ref(py);
        return liquefy(py, expr, available_vars);
    }

    if b.downcast::<SAbstraction>().is_ok() {
        return Ok(None);
    }

    if let Ok(sta) = b.downcast::<STypeApplication>() {
        let body = sta.borrow().body.clone_ref(py);
        return liquefy(py, body, available_vars);
    }

    if let Ok(sra) = b.downcast::<SRefinementApplication>() {
        let body = sra.borrow().body.clone_ref(py);
        return liquefy(py, body, available_vars);
    }

    if let Ok(sta) = b.downcast::<STypeAbstraction>() {
        let body = sta.borrow().body.clone_ref(py);
        return liquefy(py, body, available_vars);
    }

    if let Ok(sra) = b.downcast::<SRefinementAbstraction>() {
        let body = sra.borrow().body.clone_ref(py);
        return liquefy(py, body, available_vars);
    }

    if b.downcast::<SApplication>().is_ok() {
        return liquefy_app(py, t.clone_ref(py), &available_vars);
    }

    if let Ok(sl) = b.downcast::<SLet>() {
        let sl = sl.borrow();
        let name = sl.var_name.clone_ref(py);
        let val = sl.var_value.clone_ref(py);
        let body = sl.body.clone_ref(py);
        drop(sl);
        let av_dup = available_vars.as_ref().map(|v| v.clone_ref(py));
        let lval = liquefy(py, val, av_dup)?;
        let lbody = liquefy(py, body, available_vars)?;
        match (lval, lbody) {
            (Some(v), Some(b)) => Ok(Some(substitution_in_liquid(py, b, v, name)?)),
            _ => Ok(None),
        }
    } else if let Ok(sr) = b.downcast::<SRec>() {
        let sr = sr.borrow();
        let name = sr.var_name.clone_ref(py);
        let val = sr.var_value.clone_ref(py);
        let body = sr.body.clone_ref(py);
        drop(sr);
        let av_dup = available_vars.as_ref().map(|v| v.clone_ref(py));
        let lval = liquefy(py, val, av_dup)?;
        let lbody = liquefy(py, body, available_vars)?;
        match (lval, lbody) {
            (Some(v), Some(b)) => Ok(Some(substitution_in_liquid(py, b, v, name)?)),
            _ => Ok(None),
        }
    } else if let Ok(sh) = b.downcast::<SHole>() {
        let sh = sh.borrow();
        let name = sh.name.clone_ref(py);
        let loc = sh.loc.clone_ref(py);
        drop(sh);
        let argtypes = PyList::empty_bound(py);
        if let Some(av) = available_vars.as_ref() {
            let av_b = av.bind(py);
            for i in 0..av_b.len() {
                let tup = av_b.get_item(i)?;
                let xname: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
                let xty = tup.get_item(1)?.unbind();
                let lv = Py::new(py, (LiquidVar { name: xname, loc: crate::loc::default_location(py) }, LiquidTerm))?;
                let t2 = pyo3::types::PyTuple::new_bound(py, &[lv.into_any(), xty]).unbind();
                argtypes.append(t2)?;
            }
        }
        Ok(Some(
            Py::new(
                py,
                (LiquidHornApplication { name, argtypes: argtypes.unbind(), loc }, LiquidTerm),
            )?
            .into_any(),
        ))
    } else {
        Err(pyo3::exceptions::PyAssertionError::new_err(format!(
            "liquefy: unhandled {}",
            t.bind(py).str()?
        )))
    }
}

/// basic_type: unwrap a Type (Refined? TypeConstructor? TypeVar? Top?) to
/// either a TypeConstructor or a TypeVar — useful for available_vars entries.
fn basic_type(py: Python<'_>, ty: PyObject) -> PyResult<PyObject> {
    let b = ty.bind(py);
    if b.downcast::<TypeConstructor>().is_ok() || b.downcast::<TypeVar>().is_ok() {
        return Ok(ty);
    }
    if let Ok(rt) = b.downcast::<RefinedType>() {
        let inner = rt.borrow().type_.clone_ref(py);
        return basic_type(py, inner);
    }
    if b.downcast::<Top>().is_ok() {
        return t_unit(py);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unknown base type {}",
        b.str()?
    )))
}

/// Converts surface types into core types.
#[pyfunction]
#[pyo3(signature = (ty, available_vars = None))]
pub fn type_to_core(
    py: Python<'_>,
    ty: PyObject,
    available_vars: Option<Py<PyList>>,
) -> PyResult<PyObject> {
    let available_vars = available_vars.unwrap_or_else(|| PyList::empty_bound(py).unbind());

    let normalized = normalize(py, ty)?;
    let nb = normalized.bind(py);

    // Top
    if let Ok(stc) = nb.downcast::<STypeConstructor>() {
        let stc_b = stc.borrow();
        let n = stc_b.name.borrow(py);
        if n.id == 0 && n.name == "Top" {
            drop(n);
            drop(stc_b);
            let top = Py::new(py, (Top { loc: crate::loc::default_location(py) }, Type))?;
            return Ok(top.into_any());
        }
    }

    if let Ok(stv) = nb.downcast::<STypeVar>() {
        let stv = stv.borrow();
        let name = stv.name.clone_ref(py);
        let loc = stv.loc.clone_ref(py);
        drop(stv);
        let tv = Py::new(py, (TypeVar { name, loc }, Type))?;
        return Ok(tv.into_any());
    }

    if let Ok(sat) = nb.downcast::<SAbstractionType>() {
        let sat = sat.borrow();
        let oname = sat.var_name.clone_ref(py);
        let vty = sat.var_type.clone_ref(py);
        let rty = sat.type_.clone_ref(py);
        let loc = sat.loc.clone_ref(py);
        let mult = sat.multiplicity.clone_ref(py);
        drop(sat);

        // Fresh name id, retain string.
        let oname_b = oname.borrow(py);
        let oname_str = oname_b.name.clone();
        drop(oname_b);
        let new_id = next_fresh_id(py)?;
        let nname = Py::new(py, Name { name: oname_str, id: new_id })?;

        let at = type_to_core(py, vty, Some(clone_list_ref(py, &available_vars)))?;

        let mut nrty = rty;
        let mut new_av_obj = available_vars.clone_ref(py);
        let at_b = at.bind(py);
        if at_b.downcast::<TypeConstructor>().is_ok()
            || at_b.downcast::<TypeVar>().is_ok()
            || at_b.downcast::<RefinedType>().is_ok()
        {
            // Append (nname, basic_type(at)) to available_vars.
            let appended = PyList::empty_bound(py);
            let av_b = available_vars.bind(py);
            for i in 0..av_b.len() {
                appended.append(av_b.get_item(i)?)?;
            }
            let bt = basic_type(py, at.clone_ref(py))?;
            let tup = pyo3::types::PyTuple::new_bound(py, &[nname.clone_ref(py).into_any(), bt]).unbind();
            appended.append(tup)?;
            new_av_obj = appended.unbind();
            let sv = Py::new(py, (SVar { name: nname.clone_ref(py), loc: crate::loc::default_location(py) }, STerm))?.into_any();
            nrty = substitution_sterm_in_stype(py, nrty, sv, oname.clone_ref(py))?;
        }
        let new_rty = type_to_core(py, nrty, Some(new_av_obj))?;

        let ab = Py::new(
            py,
            (
                AbstractionType {
                    var_name: nname,
                    var_type: at,
                    type_: new_rty,
                    loc,
                    multiplicity: mult,
                },
                Type,
            ),
        )?;
        return Ok(ab.into_any());
    }

    if let Ok(stp) = nb.downcast::<STypePolymorphism>() {
        let stp = stp.borrow();
        let name = stp.name.clone_ref(py);
        let kind = stp.kind.clone_ref(py);
        let body = stp.body.clone_ref(py);
        let loc = stp.loc.clone_ref(py);
        drop(stp);
        let new_body = type_to_core(py, body, Some(clone_list_ref(py, &available_vars)))?;
        let tp = Py::new(
            py,
            (TypePolymorphism { name, kind, body: new_body, loc }, Type),
        )?;
        return Ok(tp.into_any());
    }

    if let Ok(srp) = nb.downcast::<SRefinementPolymorphism>() {
        let srp = srp.borrow();
        let name = srp.name.clone_ref(py);
        let sort = srp.sort.clone_ref(py);
        let body = srp.body.clone_ref(py);
        let loc = srp.loc.clone_ref(py);
        drop(srp);
        let new_sort = type_to_core(py, sort, Some(clone_list_ref(py, &available_vars)))?;
        let new_body = type_to_core(py, body, Some(clone_list_ref(py, &available_vars)))?;
        let rp = Py::new(
            py,
            (
                RefinementPolymorphism { name, sort: new_sort, body: new_body, loc },
                Type,
            ),
        )?;
        return Ok(rp.into_any());
    }

    if let Ok(srt) = nb.downcast::<SRefinedType>() {
        let srt = srt.borrow();
        let oname = srt.name.clone_ref(py);
        let ity = srt.type_.clone_ref(py);
        let refn = srt.refinement.clone_ref(py);
        let loc = srt.loc.clone_ref(py);
        drop(srt);

        let oname_b = oname.borrow(py);
        let oname_id = oname_b.id;
        let oname_str = oname_b.name.clone();
        drop(oname_b);
        let (name, refn2) = if oname_id == -1 {
            let new_id = next_fresh_id(py)?;
            let nname = Py::new(py, Name { name: oname_str, id: new_id })?;
            let sv = Py::new(py, (SVar { name: nname.clone_ref(py), loc: crate::loc::default_location(py) }, STerm))?.into_any();
            let new_ref = substitution_sterm_in_sterm(py, refn, sv, oname)?;
            (nname, new_ref)
        } else {
            (oname, refn)
        };

        let basety = type_to_core(py, ity, Some(clone_list_ref(py, &available_vars)))?;
        let basety_b = basety.bind(py);
        if !(basety_b.downcast::<TypeConstructor>().is_ok() || basety_b.downcast::<TypeVar>().is_ok()) {
            return Err(pyo3::exceptions::PyAssertionError::new_err(
                "RefinedType inner must be TypeConstructor or TypeVar",
            ));
        }
        drop(basety_b);
        // available_vars + [(name, basety)]
        let new_av = PyList::empty_bound(py);
        let av_b = available_vars.bind(py);
        for i in 0..av_b.len() {
            new_av.append(av_b.get_item(i)?)?;
        }
        let tup = pyo3::types::PyTuple::new_bound(
            py,
            &[name.clone_ref(py).into_any(), basety.clone_ref(py)],
        )
        .unbind();
        new_av.append(tup)?;
        let lref = match liquefy(py, refn2, Some(new_av.unbind()))? {
            Some(l) => l,
            None => {
                return Err(LiquefactionException::new_err(
                    "Refinement did not lower to a liquid term",
                ))
            }
        };
        let rt = Py::new(
            py,
            (
                RefinedType { name, type_: basety, refinement: lref, loc },
                Type,
            ),
        )?;
        return Ok(rt.into_any());
    }

    if let Ok(stc) = nb.downcast::<STypeConstructor>() {
        let stc = stc.borrow();
        let name = stc.name.clone_ref(py);
        let args_o = stc.args.clone_ref(py);
        let loc = stc.loc.clone_ref(py);
        drop(stc);
        let new_args = PyList::empty_bound(py);
        let av_b = args_o.bind(py);
        for i in 0..av_b.len() {
            let item = av_b.get_item(i)?.unbind();
            let nitem = type_to_core(py, item, Some(clone_list_ref(py, &available_vars)))?;
            new_args.append(nitem)?;
        }
        let tc = Py::new(
            py,
            (
                TypeConstructor { name, args: new_args.unbind(), loc },
                Type,
            ),
        )?;
        return Ok(tc.into_any());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unknown {} / {}",
        ty_repr(py, &normalized)?,
        ty_repr(py, &normalize(py, normalized.clone_ref(py))?)?,
    )))
}

fn ty_repr(py: Python<'_>, o: &PyObject) -> PyResult<String> {
    Ok(o.bind(py).str()?.to_string())
}

fn clone_list_ref(py: Python<'_>, l: &Py<PyList>) -> Py<PyList> {
    l.clone_ref(py)
}

/// Lowers a surface term into a core term.
#[pyfunction]
pub fn lower_to_core(py: Python<'_>, t: PyObject) -> PyResult<PyObject> {
    let b = t.bind(py);

    if let Ok(sh) = b.downcast::<SHole>() {
        let sh = sh.borrow();
        let name = sh.name.clone_ref(py);
        let loc = sh.loc.clone_ref(py);
        drop(sh);
        return Ok(Py::new(py, (Hole { name, loc }, Term))?.into_any());
    }

    if let Ok(slit) = b.downcast::<SLiteral>() {
        let slit = slit.borrow();
        let value = slit.value.clone_ref(py);
        let ty = slit.type_.clone_ref(py);
        let loc = slit.loc.clone_ref(py);
        drop(slit);
        let nty = type_to_core(py, ty, None)?;
        return Ok(Py::new(py, (Literal { value, type_: nty, loc }, Term))?.into_any());
    }

    if let Ok(sv) = b.downcast::<SVar>() {
        let sv = sv.borrow();
        let name = sv.name.clone_ref(py);
        let loc = sv.loc.clone_ref(py);
        drop(sv);
        return Ok(Py::new(py, (Var { name, loc }, Term))?.into_any());
    }

    if let Ok(sif) = b.downcast::<SIf>() {
        let sif = sif.borrow();
        let cond = sif.cond.clone_ref(py);
        let then = sif.then.clone_ref(py);
        let otherwise = sif.otherwise.clone_ref(py);
        let loc = sif.loc.clone_ref(py);
        drop(sif);
        let nc = lower_to_core(py, cond)?;
        let nt = lower_to_core(py, then)?;
        let no = lower_to_core(py, otherwise)?;
        return Ok(Py::new(
            py,
            (If { cond: nc, then: nt, otherwise: no, loc }, Term),
        )?
        .into_any());
    }

    if let Ok(sap) = b.downcast::<SApplication>() {
        let sap = sap.borrow();
        let fun = sap.fun.clone_ref(py);
        let arg = sap.arg.clone_ref(py);
        let loc = sap.loc.clone_ref(py);
        drop(sap);
        let nf = lower_to_core(py, fun)?;
        let na = lower_to_core(py, arg)?;
        return Ok(Py::new(py, (Application { fun: nf, arg: na, loc }, Term))?.into_any());
    }

    if let Ok(sl) = b.downcast::<SLet>() {
        let sl = sl.borrow();
        let name = sl.var_name.clone_ref(py);
        let val = sl.var_value.clone_ref(py);
        let body = sl.body.clone_ref(py);
        let loc = sl.loc.clone_ref(py);
        let mult = sl.multiplicity.clone_ref(py);
        drop(sl);
        let nv = lower_to_core(py, val)?;
        let nb = lower_to_core(py, body)?;
        return Ok(Py::new(
            py,
            (
                Let { var_name: name, var_value: nv, body: nb, loc, multiplicity: mult },
                Term,
            ),
        )?
        .into_any());
    }

    if let Ok(sr) = b.downcast::<SRec>() {
        let sr = sr.borrow();
        let name = sr.var_name.clone_ref(py);
        let ty = sr.var_type.clone_ref(py);
        let val = sr.var_value.clone_ref(py);
        let body = sr.body.clone_ref(py);
        let decr = sr.decreasing_by.clone_ref(py);
        let loc = sr.loc.clone_ref(py);
        let mult = sr.multiplicity.clone_ref(py);
        drop(sr);
        let nty = type_to_core(py, ty, None)?;
        let nv = lower_to_core(py, val)?;
        let nb = lower_to_core(py, body)?;
        // decreasing_by tuple → tuple of core
        let decr_b = decr.bind(py);
        let mut new_decr_vec: Vec<PyObject> = Vec::with_capacity(decr_b.len());
        for i in 0..decr_b.len() {
            let m = decr_b.get_item(i)?.unbind();
            new_decr_vec.push(lower_to_core(py, m)?);
        }
        let new_decr = pyo3::types::PyTuple::new_bound(py, new_decr_vec).unbind();
        return Ok(Py::new(
            py,
            (
                Rec {
                    var_name: name,
                    var_type: nty,
                    var_value: nv,
                    body: nb,
                    decreasing_by: new_decr,
                    loc,
                    multiplicity: mult,
                },
                Term,
            ),
        )?
        .into_any());
    }

    if let Ok(sa) = b.downcast::<SAnnotation>() {
        let sa = sa.borrow();
        let expr = sa.expr.clone_ref(py);
        let ty = sa.type_.clone_ref(py);
        let loc = sa.loc.clone_ref(py);
        drop(sa);
        let ne = lower_to_core(py, expr)?;
        let nt = type_to_core(py, ty, None)?;
        return Ok(Py::new(py, (Annotation { expr: ne, type_: nt, loc }, Term))?.into_any());
    }

    if let Ok(sab) = b.downcast::<SAbstraction>() {
        let sab = sab.borrow();
        let name = sab.var_name.clone_ref(py);
        let body = sab.body.clone_ref(py);
        let loc = sab.loc.clone_ref(py);
        drop(sab);
        let nb = lower_to_core(py, body)?;
        return Ok(Py::new(py, (Abstraction { var_name: name, body: nb, loc }, Term))?.into_any());
    }

    if let Ok(sta) = b.downcast::<STypeApplication>() {
        let sta = sta.borrow();
        let expr = sta.body.clone_ref(py);
        let ty = sta.type_.clone_ref(py);
        let loc = sta.loc.clone_ref(py);
        drop(sta);
        let ne = lower_to_core(py, expr)?;
        let nt = type_to_core(py, ty, None)?;
        return Ok(Py::new(py, (TypeApplication { body: ne, type_: nt, loc }, Term))?.into_any());
    }

    if let Ok(sra) = b.downcast::<SRefinementApplication>() {
        let sra = sra.borrow();
        let body = sra.body.clone_ref(py);
        let refn = sra.refinement.clone_ref(py);
        let loc = sra.loc.clone_ref(py);
        drop(sra);
        let nb = lower_to_core(py, body)?;
        let nr = lower_to_core(py, refn)?;
        return Ok(Py::new(
            py,
            (RefinementApplication { body: nb, refinement: nr, loc }, Term),
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
        let nb = lower_to_core(py, body)?;
        return Ok(Py::new(
            py,
            (TypeAbstraction { name, kind, body: nb, loc }, Term),
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
        let nsort = type_to_core(py, sort, None)?;
        let nb = lower_to_core(py, body)?;
        return Ok(Py::new(
            py,
            (
                RefinementAbstraction { name, sort: nsort, body: nb, loc },
                Term,
            ),
        )?
        .into_any());
    }

    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "{} not supported",
        b.str()?
    )))
}

/// Monomorphize a polymorphic type by instantiating every type-variable to Int.
/// Used to wrap uninterpreted function types.
fn monomorphic_type(py: Python<'_>, ty: PyObject) -> PyResult<PyObject> {
    let b = ty.bind(py);
    if let Ok(tp) = b.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let name = tp.name.clone_ref(py);
        let body = tp.body.clone_ref(py);
        drop(tp);
        let int_ty = t_int(py)?;
        let new_body = substitute_vartype(py, body, int_ty, name)?;
        return monomorphic_type(py, new_body);
    }
    if b.downcast::<AbstractionType>().is_ok() {
        return Ok(ty);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Type {} is not a monomorphic type, cannot be used in uninterpreted binders.",
        b.str()?
    )))
}

fn wrap_ctx_entry(py: Python<'_>, entry: &Bound<'_, PyAny>) -> PyResult<PyObject> {
    if let Ok(vb) = entry.downcast::<ElabVariableBinder>() {
        let vb = vb.borrow();
        let name = vb.name.clone_ref(py);
        let ty = vb.type_.clone_ref(py);
        drop(vb);
        let nty = type_to_core(py, ty, None)?;
        let pe = Py::new(
            py,
            (VariableBinder { name, type_: nty }, TypingContextEntry),
        )?;
        return Ok(pe.into_any());
    }
    if let Ok(ub) = entry.downcast::<ElabUninterpretedBinder>() {
        let ub = ub.borrow();
        let name = ub.name.clone_ref(py);
        let ty = ub.type_.clone_ref(py);
        drop(ub);
        let absty = type_to_core(py, ty, None)?;
        let concrete = monomorphic_type(py, absty)?;
        let pe = Py::new(
            py,
            (UninterpretedBinder { name, type_: concrete }, TypingContextEntry),
        )?;
        return Ok(pe.into_any());
    }
    if let Ok(tv) = entry.downcast::<ElabTypeVarBinder>() {
        let tv = tv.borrow();
        let name = tv.name.clone_ref(py);
        let kind = tv.type_.clone_ref(py);
        drop(tv);
        let pe = Py::new(
            py,
            (
                TypeBinder { type_name: name, type_kind: kind },
                TypingContextEntry,
            ),
        )?;
        return Ok(pe.into_any());
    }
    if let Ok(td) = entry.downcast::<ElabTypeDecl>() {
        let td = td.borrow();
        let name = td.name.clone_ref(py);
        let args = td.args.clone_ref(py);
        drop(td);
        let pe = Py::new(
            py,
            (TypeConstructorBinder { name, args }, TypingContextEntry),
        )?;
        return Ok(pe.into_any());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "{} not supported in Core",
        entry.str()?
    )))
}

/// Lower the elaboration context to the core typing context.
#[pyfunction]
pub fn lower_to_core_context(
    py: Python<'_>,
    elctx: &ElaborationTypingContext,
) -> PyResult<PyObject> {
    let entries = elctx.entries.bind(py);
    let new_entries = PyList::empty_bound(py);
    for i in 0..entries.len() {
        let entry = entries.get_item(i)?;
        let new_e = wrap_ctx_entry(py, &entry)?;
        new_entries.append(new_e)?;
    }
    // Invoke the TypingContext constructor so __new__ prepends builtin types.
    let tc_cls = py.get_type_bound::<TypingContext>();
    let tc = tc_cls.call1((new_entries.unbind(),))?;
    Ok(tc.unbind())
}

// Silence unused warning for the Top sentinel import.
#[allow(dead_code)]
fn _force_top(_py: Python<'_>) -> PyResult<()> {
    let _: PyObject;
    Ok(())
}

// Silence the warning that we only use default_multiplicity to keep it
// referenced for consistency.
#[allow(dead_code)]
fn _force_mult(py: Python<'_>) -> PyObject {
    default_multiplicity(py)
}
