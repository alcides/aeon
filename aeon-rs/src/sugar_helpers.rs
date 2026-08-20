//! Sugar-AST helpers (port of `aeon/sugar/ast_helpers.py`,
//! `aeon/sugar/equality.py`, `aeon/sugar/lifting.py`,
//! `aeon/sugar/substitutions.py`).
//!
//! These are all pure structural walks over the sugar AST.

use std::collections::HashMap;

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::liquid::{
    LiquidApp, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt, LiquidLiteralString,
    LiquidVar,
};
use crate::name::Name;
use crate::sugar::{
    SAbstraction, SAbstractionType, SAnonConstructor, SAnnotation, SApplication, SBy, SHole, SIf,
    SLet, SLiteral, SMatch, SMatchBranch, SQualifiedVar, SRec, SRefinedType,
    SRefinementAbstraction, SRefinementApplication, SRefinementPolymorphism, STerm, SType,
    STypeAbstraction, STypeApplication, STypeConstructor, STypePolymorphism, STypeVar, SVar,
};
use crate::terms::{
    Abstraction, Annotation, Application, Hole, If, Let, Literal, Rec, RefinementAbstraction,
    RefinementApplication, TypeAbstraction, TypeApplication, Var,
};
use crate::liquid::LiquidHornApplication;
use crate::types::{
    AbstractionType, RefinedType, RefinementPolymorphism, Top, TypeConstructor, TypePolymorphism,
    TypeVar,
};

// =============================================================================
// type_equality / term_equality — alpha-renaming-aware structural equality.
// =============================================================================

#[derive(Clone, PartialEq, Eq, Hash)]
struct NameKey {
    name: String,
    id: i64,
}

fn nk(py: Python<'_>, n: &Py<Name>) -> NameKey {
    let n = n.borrow(py);
    NameKey { name: n.name.clone(), id: n.id }
}

fn names_equal(py: Python<'_>, a: &Py<Name>, b: &Py<Name>) -> bool {
    nk(py, a) == nk(py, b)
}

type Rename = HashMap<NameKey, Py<Name>>;

fn lookup_rename(py: Python<'_>, r: &Rename, a: &Py<Name>) -> Py<Name> {
    let k = nk(py, a);
    r.get(&k).map(|n| n.clone_ref(py)).unwrap_or_else(|| a.clone_ref(py))
}

fn extend(py: Python<'_>, r: &Rename, a: &Py<Name>, b: &Py<Name>) -> Rename {
    let mut out: Rename = r.iter().map(|(k, v)| (k.clone(), v.clone_ref(py))).collect();
    out.insert(nk(py, a), b.clone_ref(py));
    out
}

fn dict_to_rename(py: Python<'_>, d: Option<&Bound<'_, pyo3::types::PyDict>>) -> PyResult<Rename> {
    let mut out: Rename = HashMap::new();
    if let Some(d) = d {
        for (k, v) in d.iter() {
            let kn: Py<Name> = k.downcast::<Name>()?.clone().unbind();
            let vn: Py<Name> = v.downcast::<Name>()?.clone().unbind();
            out.insert(nk(py, &kn), vn);
        }
    }
    Ok(out)
}

fn type_equality_inner(py: Python<'_>, a: &PyObject, b: &PyObject, rl: &Rename) -> PyResult<bool> {
    let ab = a.bind(py);
    let bb = b.bind(py);
    if let (Ok(av), Ok(bv)) = (ab.downcast::<STypeVar>(), bb.downcast::<STypeVar>()) {
        let an = av.borrow().name.clone_ref(py);
        let bn = bv.borrow().name.clone_ref(py);
        return Ok(names_equal(py, &lookup_rename(py, rl, &an), &bn));
    }
    if let (Ok(art), Ok(brt)) = (ab.downcast::<SRefinedType>(), bb.downcast::<SRefinedType>()) {
        let art = art.borrow();
        let brt = brt.borrow();
        let new_rl = extend(py, rl, &art.name, &brt.name);
        let aty = art.type_.clone_ref(py);
        let aref = art.refinement.clone_ref(py);
        let bty = brt.type_.clone_ref(py);
        let bref = brt.refinement.clone_ref(py);
        drop(art);
        drop(brt);
        if !type_equality_inner(py, &aty, &bty, &new_rl)? {
            return Ok(false);
        }
        return term_equality_inner(py, &aref, &bref, &new_rl);
    }
    if let (Ok(aat), Ok(bat)) = (
        ab.downcast::<SAbstractionType>(),
        bb.downcast::<SAbstractionType>(),
    ) {
        let aat = aat.borrow();
        let bat = bat.borrow();
        let avn = aat.var_name.clone_ref(py);
        let avt = aat.var_type.clone_ref(py);
        let art = aat.type_.clone_ref(py);
        let bvn = bat.var_name.clone_ref(py);
        let bvt = bat.var_type.clone_ref(py);
        let brt = bat.type_.clone_ref(py);
        drop(aat);
        drop(bat);
        if !type_equality_inner(py, &avt, &bvt, rl)? {
            return Ok(false);
        }
        let new_rl = extend(py, rl, &avn, &bvn);
        return type_equality_inner(py, &art, &brt, &new_rl);
    }
    if let (Ok(atc), Ok(btc)) = (
        ab.downcast::<STypeConstructor>(),
        bb.downcast::<STypeConstructor>(),
    ) {
        let atc = atc.borrow();
        let btc = btc.borrow();
        let an = atc.name.clone_ref(py);
        let bn = btc.name.clone_ref(py);
        if !names_equal(py, &an, &bn) {
            return Ok(false);
        }
        let aa = atc.args.clone_ref(py);
        let ba = btc.args.clone_ref(py);
        drop(atc);
        drop(btc);
        let ab_l = aa.bind(py);
        let bb_l = ba.bind(py);
        if ab_l.len() != bb_l.len() {
            return Ok(false);
        }
        for i in 0..ab_l.len() {
            let ai = ab_l.get_item(i)?.unbind();
            let bi = bb_l.get_item(i)?.unbind();
            if !type_equality_inner(py, &ai, &bi, rl)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if let (Ok(atp), Ok(btp)) = (
        ab.downcast::<STypePolymorphism>(),
        bb.downcast::<STypePolymorphism>(),
    ) {
        let atp = atp.borrow();
        let btp = btp.borrow();
        let ak = atp.kind.clone_ref(py);
        let bk = btp.kind.clone_ref(py);
        if !ak.bind(py).eq(bk.bind(py))? {
            return Ok(false);
        }
        let abdy = atp.body.clone_ref(py);
        let bbdy = btp.body.clone_ref(py);
        let an = atp.name.clone_ref(py);
        let bn = btp.name.clone_ref(py);
        drop(atp);
        drop(btp);
        let new_rl = extend(py, rl, &an, &bn);
        return type_equality_inner(py, &abdy, &bbdy, &new_rl);
    }
    if let (Ok(arp), Ok(brp)) = (
        ab.downcast::<SRefinementPolymorphism>(),
        bb.downcast::<SRefinementPolymorphism>(),
    ) {
        let arp = arp.borrow();
        let brp = brp.borrow();
        let asort = arp.sort.clone_ref(py);
        let bsort = brp.sort.clone_ref(py);
        let abdy = arp.body.clone_ref(py);
        let bbdy = brp.body.clone_ref(py);
        let an = arp.name.clone_ref(py);
        let bn = brp.name.clone_ref(py);
        drop(arp);
        drop(brp);
        if !type_equality_inner(py, &asort, &bsort, rl)? {
            return Ok(false);
        }
        let new_rl = extend(py, rl, &an, &bn);
        return type_equality_inner(py, &abdy, &bbdy, &new_rl);
    }
    if let (Ok(atap), Ok(btap)) = (
        ab.downcast::<STypeApplication>(),
        bb.downcast::<STypeApplication>(),
    ) {
        let atap = atap.borrow();
        let btap = btap.borrow();
        let abdy = atap.body.clone_ref(py);
        let aty = atap.type_.clone_ref(py);
        let bbdy = btap.body.clone_ref(py);
        let bty = btap.type_.clone_ref(py);
        drop(atap);
        drop(btap);
        if !term_equality_inner(py, &abdy, &bbdy, rl)? {
            return Ok(false);
        }
        return type_equality_inner(py, &aty, &bty, rl);
    }
    if let (Ok(ata), Ok(bta)) = (
        ab.downcast::<STypeAbstraction>(),
        bb.downcast::<STypeAbstraction>(),
    ) {
        let ata = ata.borrow();
        let bta = bta.borrow();
        let ak = ata.kind.clone_ref(py);
        let bk = bta.kind.clone_ref(py);
        if !ak.bind(py).eq(bk.bind(py))? {
            return Ok(false);
        }
        let abdy = ata.body.clone_ref(py);
        let bbdy = bta.body.clone_ref(py);
        let an = ata.name.clone_ref(py);
        let bn = bta.name.clone_ref(py);
        drop(ata);
        drop(bta);
        let new_rl = extend(py, rl, &an, &bn);
        return term_equality_inner(py, &abdy, &bbdy, &new_rl);
    }
    Ok(false)
}

fn term_equality_inner(py: Python<'_>, a: &PyObject, b: &PyObject, rl: &Rename) -> PyResult<bool> {
    let ab = a.bind(py);
    let bb = b.bind(py);
    if let (Ok(av), Ok(bv)) = (ab.downcast::<SVar>(), bb.downcast::<SVar>()) {
        let an = av.borrow().name.clone_ref(py);
        let bn = bv.borrow().name.clone_ref(py);
        return Ok(names_equal(py, &lookup_rename(py, rl, &an), &bn));
    }
    if let (Ok(av), Ok(bv)) = (ab.downcast::<SHole>(), bb.downcast::<SHole>()) {
        let an = av.borrow().name.clone_ref(py);
        let bn = bv.borrow().name.clone_ref(py);
        return Ok(names_equal(py, &lookup_rename(py, rl, &an), &bn));
    }
    if let (Ok(av), Ok(bv)) = (ab.downcast::<SBy>(), bb.downcast::<SBy>()) {
        return av.borrow().steps.bind(py).eq(bv.borrow().steps.bind(py));
    }
    if let (Ok(av), Ok(bv)) = (ab.downcast::<SLiteral>(), bb.downcast::<SLiteral>()) {
        let av = av.borrow();
        let bv = bv.borrow();
        if !av.value.bind(py).eq(bv.value.bind(py))? {
            return Ok(false);
        }
        return av.type_.bind(py).eq(bv.type_.bind(py));
    }
    if let (Ok(av), Ok(bv)) = (ab.downcast::<SApplication>(), bb.downcast::<SApplication>()) {
        let av = av.borrow();
        let bv = bv.borrow();
        let a1 = av.fun.clone_ref(py);
        let a2 = av.arg.clone_ref(py);
        let b1 = bv.fun.clone_ref(py);
        let b2 = bv.arg.clone_ref(py);
        drop(av);
        drop(bv);
        if !term_equality_inner(py, &a1, &b1, rl)? {
            return Ok(false);
        }
        return term_equality_inner(py, &a2, &b2, rl);
    }
    if let (Ok(av), Ok(bv)) = (ab.downcast::<SAbstraction>(), bb.downcast::<SAbstraction>()) {
        let av = av.borrow();
        let bv = bv.borrow();
        let an = av.var_name.clone_ref(py);
        let bn = bv.var_name.clone_ref(py);
        let abdy = av.body.clone_ref(py);
        let bbdy = bv.body.clone_ref(py);
        drop(av);
        drop(bv);
        let new_rl = extend(py, rl, &an, &bn);
        return term_equality_inner(py, &abdy, &bbdy, &new_rl);
    }
    if let (Ok(av), Ok(bv)) = (ab.downcast::<SLet>(), bb.downcast::<SLet>()) {
        let av = av.borrow();
        let bv = bv.borrow();
        let an = av.var_name.clone_ref(py);
        let aval = av.var_value.clone_ref(py);
        let abdy = av.body.clone_ref(py);
        let bn = bv.var_name.clone_ref(py);
        let bval = bv.var_value.clone_ref(py);
        let bbdy = bv.body.clone_ref(py);
        drop(av);
        drop(bv);
        if !term_equality_inner(py, &aval, &bval, rl)? {
            return Ok(false);
        }
        let new_rl = extend(py, rl, &an, &bn);
        return term_equality_inner(py, &abdy, &bbdy, &new_rl);
    }
    if let (Ok(av), Ok(bv)) = (ab.downcast::<SRec>(), bb.downcast::<SRec>()) {
        let av = av.borrow();
        let bv = bv.borrow();
        let an = av.var_name.clone_ref(py);
        let aty = av.var_type.clone_ref(py);
        let aval = av.var_value.clone_ref(py);
        let abdy = av.body.clone_ref(py);
        let adecr = av.decreasing_by.clone_ref(py);
        let bn = bv.var_name.clone_ref(py);
        let bty = bv.var_type.clone_ref(py);
        let bval = bv.var_value.clone_ref(py);
        let bbdy = bv.body.clone_ref(py);
        let bdecr = bv.decreasing_by.clone_ref(py);
        drop(av);
        drop(bv);
        let new_rl = extend(py, rl, &an, &bn);
        if !term_equality_inner(py, &aval, &bval, &new_rl)? {
            return Ok(false);
        }
        if !type_equality_inner(py, &aty, &bty, rl)? {
            return Ok(false);
        }
        if !term_equality_inner(py, &abdy, &bbdy, &new_rl)? {
            return Ok(false);
        }
        let ad = adecr.bind(py);
        let bd = bdecr.bind(py);
        if ad.len() != bd.len() {
            return Ok(false);
        }
        for i in 0..ad.len() {
            let xi = ad.get_item(i)?.unbind();
            let yi = bd.get_item(i)?.unbind();
            if !term_equality_inner(py, &xi, &yi, &new_rl)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if let (Ok(av), Ok(bv)) = (ab.downcast::<SAnnotation>(), bb.downcast::<SAnnotation>()) {
        let av = av.borrow();
        let bv = bv.borrow();
        let aexp = av.expr.clone_ref(py);
        let aty = av.type_.clone_ref(py);
        let bexp = bv.expr.clone_ref(py);
        let bty = bv.type_.clone_ref(py);
        drop(av);
        drop(bv);
        if !term_equality_inner(py, &aexp, &bexp, rl)? {
            return Ok(false);
        }
        return type_equality_inner(py, &aty, &bty, rl);
    }
    if let (Ok(av), Ok(bv)) = (ab.downcast::<SIf>(), bb.downcast::<SIf>()) {
        let av = av.borrow();
        let bv = bv.borrow();
        let ac = av.cond.clone_ref(py);
        let at = av.then.clone_ref(py);
        let ao = av.otherwise.clone_ref(py);
        let bc = bv.cond.clone_ref(py);
        let bt = bv.then.clone_ref(py);
        let bo = bv.otherwise.clone_ref(py);
        drop(av);
        drop(bv);
        return Ok(term_equality_inner(py, &ac, &bc, rl)?
            && term_equality_inner(py, &at, &bt, rl)?
            && term_equality_inner(py, &ao, &bo, rl)?);
    }
    if let (Ok(av), Ok(bv)) = (
        ab.downcast::<STypeApplication>(),
        bb.downcast::<STypeApplication>(),
    ) {
        let av = av.borrow();
        let bv = bv.borrow();
        let abdy = av.body.clone_ref(py);
        let aty = av.type_.clone_ref(py);
        let bbdy = bv.body.clone_ref(py);
        let bty = bv.type_.clone_ref(py);
        drop(av);
        drop(bv);
        if !term_equality_inner(py, &abdy, &bbdy, rl)? {
            return Ok(false);
        }
        return type_equality_inner(py, &aty, &bty, rl);
    }
    if let (Ok(av), Ok(bv)) = (
        ab.downcast::<STypeAbstraction>(),
        bb.downcast::<STypeAbstraction>(),
    ) {
        let av = av.borrow();
        let bv = bv.borrow();
        let ak = av.kind.clone_ref(py);
        let bk = bv.kind.clone_ref(py);
        if !ak.bind(py).eq(bk.bind(py))? {
            return Ok(false);
        }
        let abdy = av.body.clone_ref(py);
        let bbdy = bv.body.clone_ref(py);
        let an = av.name.clone_ref(py);
        let bn = bv.name.clone_ref(py);
        drop(av);
        drop(bv);
        let new_rl = extend(py, rl, &an, &bn);
        return term_equality_inner(py, &abdy, &bbdy, &new_rl);
    }
    if let (Ok(av), Ok(bv)) = (
        ab.downcast::<SRefinementAbstraction>(),
        bb.downcast::<SRefinementAbstraction>(),
    ) {
        let av = av.borrow();
        let bv = bv.borrow();
        let asort = av.sort.clone_ref(py);
        let bsort = bv.sort.clone_ref(py);
        if !type_equality_inner(py, &asort, &bsort, rl)? {
            return Ok(false);
        }
        let abdy = av.body.clone_ref(py);
        let bbdy = bv.body.clone_ref(py);
        let an = av.name.clone_ref(py);
        let bn = bv.name.clone_ref(py);
        drop(av);
        drop(bv);
        let new_rl = extend(py, rl, &an, &bn);
        return term_equality_inner(py, &abdy, &bbdy, &new_rl);
    }
    if let (Ok(av), Ok(bv)) = (
        ab.downcast::<SRefinementApplication>(),
        bb.downcast::<SRefinementApplication>(),
    ) {
        let av = av.borrow();
        let bv = bv.borrow();
        let abdy = av.body.clone_ref(py);
        let arefn = av.refinement.clone_ref(py);
        let bbdy = bv.body.clone_ref(py);
        let brefn = bv.refinement.clone_ref(py);
        drop(av);
        drop(bv);
        return Ok(term_equality_inner(py, &abdy, &bbdy, rl)?
            && term_equality_inner(py, &arefn, &brefn, rl)?);
    }
    Ok(false)
}

#[pyfunction]
#[pyo3(signature = (a, b, rename_left = None))]
pub fn type_equality(
    py: Python<'_>,
    a: PyObject,
    b: PyObject,
    rename_left: Option<&Bound<'_, pyo3::types::PyDict>>,
) -> PyResult<bool> {
    let rl = dict_to_rename(py, rename_left)?;
    type_equality_inner(py, &a, &b, &rl)
}

#[pyfunction]
#[pyo3(signature = (a, b, rename_left = None))]
pub fn term_equality(
    py: Python<'_>,
    a: PyObject,
    b: PyObject,
    rename_left: Option<&Bound<'_, pyo3::types::PyDict>>,
) -> PyResult<bool> {
    let rl = dict_to_rename(py, rename_left)?;
    term_equality_inner(py, &a, &b, &rl)
}

// =============================================================================
// lift / lift_type / lift_liquid — Core AST → Sugar AST.
// =============================================================================

fn st_constructor(py: Python<'_>, name: &str) -> PyResult<PyObject> {
    let n = Py::new(py, Name { name: name.to_string(), id: 0 })?;
    let empty = PyList::empty_bound(py).unbind();
    Ok(Py::new(
        py,
        (
            STypeConstructor {
                name: n,
                args: empty,
                loc: crate::loc::default_location(py),
            },
            SType,
        ),
    )?
    .into_any())
}

#[pyfunction]
pub fn lift_liquid(py: Python<'_>, ref_: PyObject) -> PyResult<PyObject> {
    let b = ref_.bind(py);
    if let Ok(lb) = b.downcast::<LiquidLiteralBool>() {
        let lb = lb.borrow();
        let v = lb.value;
        let loc = lb.loc.clone_ref(py);
        drop(lb);
        return Ok(Py::new(
            py,
            (
                SLiteral { value: v.into_py(py), type_: st_constructor(py, "Bool")?, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(li) = b.downcast::<LiquidLiteralInt>() {
        let li = li.borrow();
        let v = li.value;
        let loc = li.loc.clone_ref(py);
        drop(li);
        return Ok(Py::new(
            py,
            (
                SLiteral { value: v.into_py(py), type_: st_constructor(py, "Int")?, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(lf) = b.downcast::<LiquidLiteralFloat>() {
        let lf = lf.borrow();
        let v = lf.value;
        let loc = lf.loc.clone_ref(py);
        drop(lf);
        return Ok(Py::new(
            py,
            (
                SLiteral { value: v.into_py(py), type_: st_constructor(py, "Float")?, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ls) = b.downcast::<LiquidLiteralString>() {
        let ls = ls.borrow();
        let v = ls.value.clone();
        let loc = ls.loc.clone_ref(py);
        drop(ls);
        return Ok(Py::new(
            py,
            (
                SLiteral { value: v.into_py(py), type_: st_constructor(py, "String")?, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(lv) = b.downcast::<LiquidVar>() {
        let lv = lv.borrow();
        let name = lv.name.clone_ref(py);
        let loc = lv.loc.clone_ref(py);
        drop(lv);
        return Ok(Py::new(py, (SVar { name, loc }, STerm))?.into_any());
    }
    if let Ok(la) = b.downcast::<LiquidApp>() {
        let la = la.borrow();
        let fun_name = la.fun.clone_ref(py);
        let args = la.args.clone_ref(py);
        let loc = la.loc.clone_ref(py);
        drop(la);
        let mut v: PyObject = Py::new(
            py,
            (SVar { name: fun_name, loc: loc.clone_ref(py) }, STerm),
        )?
        .into_any();
        let args_b = args.bind(py);
        for i in 0..args_b.len() {
            let arg = args_b.get_item(i)?.unbind();
            let lifted = lift_liquid(py, arg)?;
            v = Py::new(
                py,
                (
                    SApplication { fun: v, arg: lifted, loc: loc.clone_ref(py) },
                    STerm,
                ),
            )?
            .into_any();
        }
        return Ok(v);
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Don't know how to lift liquid term {}",
        b.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn lift_type(py: Python<'_>, ty: PyObject) -> PyResult<PyObject> {
    let b = ty.bind(py);
    if b.is_instance_of::<Top>() {
        return st_constructor(py, "Top");
    }
    if let Ok(tv) = b.downcast::<TypeVar>() {
        let tv = tv.borrow();
        let name = tv.name.clone_ref(py);
        let loc = tv.loc.clone_ref(py);
        drop(tv);
        return Ok(Py::new(py, (STypeVar { name, loc }, SType))?.into_any());
    }
    if let Ok(tc) = b.downcast::<TypeConstructor>() {
        let tc = tc.borrow();
        let name = tc.name.clone_ref(py);
        let args = tc.args.clone_ref(py);
        let loc = tc.loc.clone_ref(py);
        drop(tc);
        let new_args = PyList::empty_bound(py);
        let ab_l = args.bind(py);
        for i in 0..ab_l.len() {
            new_args.append(lift_type(py, ab_l.get_item(i)?.unbind())?)?;
        }
        return Ok(Py::new(
            py,
            (
                STypeConstructor { name, args: new_args.unbind(), loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(at) = b.downcast::<AbstractionType>() {
        let at = at.borrow();
        let name = at.var_name.clone_ref(py);
        let var_type = at.var_type.clone_ref(py);
        let return_type = at.type_.clone_ref(py);
        let loc = at.loc.clone_ref(py);
        let mult = at.multiplicity.clone_ref(py);
        drop(at);
        let nb = lift_type(py, var_type)?;
        let nr = lift_type(py, return_type)?;
        return Ok(Py::new(
            py,
            (
                SAbstractionType {
                    var_name: name,
                    var_type: nb,
                    type_: nr,
                    loc,
                    multiplicity: mult,
                },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(rt) = b.downcast::<RefinedType>() {
        let rt = rt.borrow();
        let name = rt.name.clone_ref(py);
        let inner = rt.type_.clone_ref(py);
        let refinement = rt.refinement.clone_ref(py);
        let loc = rt.loc.clone_ref(py);
        drop(rt);
        if refinement.bind(py).is_instance_of::<LiquidHornApplication>() {
            return lift_type(py, inner);
        }
        let nty = lift_type(py, inner)?;
        let nref = lift_liquid(py, refinement)?;
        return Ok(Py::new(
            py,
            (
                SRefinedType { name, type_: nty, refinement: nref, loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(tp) = b.downcast::<TypePolymorphism>() {
        let tp = tp.borrow();
        let name = tp.name.clone_ref(py);
        let kind = tp.kind.clone_ref(py);
        let body = tp.body.clone_ref(py);
        let loc = tp.loc.clone_ref(py);
        drop(tp);
        let nb = lift_type(py, body)?;
        return Ok(Py::new(
            py,
            (STypePolymorphism { name, kind, body: nb, loc }, SType),
        )?
        .into_any());
    }
    if let Ok(rp) = b.downcast::<RefinementPolymorphism>() {
        let rp = rp.borrow();
        let name = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        let loc = rp.loc.clone_ref(py);
        drop(rp);
        let ns = lift_type(py, sort)?;
        let nb = lift_type(py, body)?;
        return Ok(Py::new(
            py,
            (
                SRefinementPolymorphism { name, sort: ns, body: nb, loc },
                SType,
            ),
        )?
        .into_any());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Don't know how to lift type {}",
        b.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn lift(py: Python<'_>, t: PyObject) -> PyResult<PyObject> {
    let b = t.bind(py);
    if let Ok(lit) = b.downcast::<Literal>() {
        let lit = lit.borrow();
        let value = lit.value.clone_ref(py);
        let typ = lit.type_.clone_ref(py);
        let loc = lit.loc.clone_ref(py);
        drop(lit);
        return Ok(Py::new(
            py,
            (
                SLiteral { value, type_: lift_type(py, typ)?, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(v) = b.downcast::<Var>() {
        let v = v.borrow();
        return Ok(Py::new(
            py,
            (
                SVar { name: v.name.clone_ref(py), loc: v.loc.clone_ref(py) },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(an) = b.downcast::<Annotation>() {
        let an = an.borrow();
        let expr = an.expr.clone_ref(py);
        let typ = an.type_.clone_ref(py);
        let loc = an.loc.clone_ref(py);
        drop(an);
        return Ok(Py::new(
            py,
            (
                SAnnotation {
                    expr: lift(py, expr)?,
                    type_: lift_type(py, typ)?,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(h) = b.downcast::<Hole>() {
        let h = h.borrow();
        return Ok(Py::new(
            py,
            (
                SHole { name: h.name.clone_ref(py), loc: h.loc.clone_ref(py) },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(app) = b.downcast::<Application>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        let loc = app.loc.clone_ref(py);
        drop(app);
        return Ok(Py::new(
            py,
            (
                SApplication {
                    fun: lift(py, fun)?,
                    arg: lift(py, arg)?,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ab) = b.downcast::<Abstraction>() {
        let ab = ab.borrow();
        let var_name = ab.var_name.clone_ref(py);
        let body = ab.body.clone_ref(py);
        let loc = ab.loc.clone_ref(py);
        drop(ab);
        return Ok(Py::new(
            py,
            (
                SAbstraction {
                    var_name,
                    body: lift(py, body)?,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(le) = b.downcast::<Let>() {
        let le = le.borrow();
        let var_name = le.var_name.clone_ref(py);
        let var_value = le.var_value.clone_ref(py);
        let body = le.body.clone_ref(py);
        let loc = le.loc.clone_ref(py);
        let mult = le.multiplicity.clone_ref(py);
        drop(le);
        return Ok(Py::new(
            py,
            (
                SLet {
                    var_name,
                    var_value: lift(py, var_value)?,
                    body: lift(py, body)?,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(rc) = b.downcast::<Rec>() {
        let rc = rc.borrow();
        let var_name = rc.var_name.clone_ref(py);
        let var_type = rc.var_type.clone_ref(py);
        let var_value = rc.var_value.clone_ref(py);
        let body = rc.body.clone_ref(py);
        let decreasing_by = rc.decreasing_by.clone_ref(py);
        let loc = rc.loc.clone_ref(py);
        let mult = rc.multiplicity.clone_ref(py);
        drop(rc);
        let nd_list = PyList::empty_bound(py);
        let dec_b = decreasing_by.bind(py);
        for i in 0..dec_b.len() {
            nd_list.append(lift(py, dec_b.get_item(i)?.unbind())?)?;
        }
        let nd_tuple = PyTuple::new_bound(py, nd_list.iter()).unbind();
        return Ok(Py::new(
            py,
            (
                SRec {
                    var_name,
                    var_type: lift_type(py, var_type)?,
                    var_value: lift(py, var_value)?,
                    body: lift(py, body)?,
                    decreasing_by: nd_tuple,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ife) = b.downcast::<If>() {
        let ife = ife.borrow();
        let cond = ife.cond.clone_ref(py);
        let then = ife.then.clone_ref(py);
        let otherwise = ife.otherwise.clone_ref(py);
        let loc = ife.loc.clone_ref(py);
        drop(ife);
        return Ok(Py::new(
            py,
            (
                SIf {
                    cond: lift(py, cond)?,
                    then: lift(py, then)?,
                    otherwise: lift(py, otherwise)?,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ta) = b.downcast::<TypeAbstraction>() {
        let ta = ta.borrow();
        let name = ta.name.clone_ref(py);
        let kind = ta.kind.clone_ref(py);
        let body = ta.body.clone_ref(py);
        let loc = ta.loc.clone_ref(py);
        drop(ta);
        return Ok(Py::new(
            py,
            (
                STypeAbstraction {
                    name,
                    kind,
                    body: lift(py, body)?,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ra) = b.downcast::<RefinementAbstraction>() {
        let ra = ra.borrow();
        let name = ra.name.clone_ref(py);
        let sort = ra.sort.clone_ref(py);
        let body = ra.body.clone_ref(py);
        let loc = ra.loc.clone_ref(py);
        drop(ra);
        return Ok(Py::new(
            py,
            (
                SRefinementAbstraction {
                    name,
                    sort: lift_type(py, sort)?,
                    body: lift(py, body)?,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(tap) = b.downcast::<TypeApplication>() {
        let tap = tap.borrow();
        let body = tap.body.clone_ref(py);
        let typ = tap.type_.clone_ref(py);
        let loc = tap.loc.clone_ref(py);
        drop(tap);
        return Ok(Py::new(
            py,
            (
                STypeApplication {
                    body: lift(py, body)?,
                    type_: lift_type(py, typ)?,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(rap) = b.downcast::<RefinementApplication>() {
        let rap = rap.borrow();
        let body = rap.body.clone_ref(py);
        let refinement = rap.refinement.clone_ref(py);
        let loc = rap.loc.clone_ref(py);
        drop(rap);
        return Ok(Py::new(
            py,
            (
                SRefinementApplication {
                    body: lift(py, body)?,
                    refinement: lift(py, refinement)?,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Don't know how to lift {}",
        b.repr()?.to_string()
    )))
}

// =============================================================================
// Substitutions: normalize / substitute_svartype_in_stype /
// substitution_sterm_in_stype / substitution_sterm_in_sterm /
// substitute_refinement_param_in_stype / substitution_svartype_in_sterm
// =============================================================================

fn momega(py: Python<'_>) -> PyResult<PyObject> {
    Ok(py
        .import_bound("aeon.core.multiplicity")?
        .getattr("MOmega")?
        .unbind())
}

fn get_multiplicity(py: Python<'_>, ty: &PyObject) -> PyResult<PyObject> {
    match ty.bind(py).getattr("multiplicity") {
        Ok(m) => Ok(m.unbind()),
        Err(_) => momega(py),
    }
}

#[pyfunction]
pub fn normalize(py: Python<'_>, ty: PyObject) -> PyResult<PyObject> {
    let b = ty.bind(py);
    if let Ok(ort) = b.downcast::<SRefinedType>() {
        let ort = ort.borrow();
        let inner_obj = ort.type_.clone_ref(py);
        if let Ok(irt) = inner_obj.bind(py).downcast::<SRefinedType>() {
            let irt = irt.borrow();
            let oname = ort.name.clone_ref(py);
            let iname = irt.name.clone_ref(py);
            let ity = irt.type_.clone_ref(py);
            let iref = irt.refinement.clone_ref(py);
            let oref = ort.refinement.clone_ref(py);
            drop(irt);
            drop(ort);
            // Substitute iref's iname → SVar(oname), then build && oref.
            let sv = Py::new(
                py,
                (
                    SVar { name: oname.clone_ref(py), loc: crate::loc::default_location(py) },
                    STerm,
                ),
            )?
            .into_any();
            let a1 = substitution_sterm_in_sterm(py, iref, sv, iname)?;
            let and_name = Py::new(py, Name { name: "&&".to_string(), id: 0 })?;
            let var_and = Py::new(
                py,
                (
                    SVar { name: and_name, loc: crate::loc::default_location(py) },
                    STerm,
                ),
            )?
            .into_any();
            let app1 = Py::new(
                py,
                (
                    SApplication { fun: var_and, arg: a1, loc: crate::loc::default_location(py) },
                    STerm,
                ),
            )?
            .into_any();
            let new_ref = Py::new(
                py,
                (
                    SApplication { fun: app1, arg: oref, loc: crate::loc::default_location(py) },
                    STerm,
                ),
            )?
            .into_any();
            return Ok(Py::new(
                py,
                (
                    SRefinedType {
                        name: oname,
                        type_: ity,
                        refinement: new_ref,
                        loc: crate::loc::default_location(py),
                    },
                    SType,
                ),
            )?
            .into_any());
        }
    }
    Ok(ty)
}

#[pyfunction]
pub fn substitute_svartype_in_stype(
    py: Python<'_>,
    ty: PyObject,
    beta: PyObject,
    alpha: Py<Name>,
) -> PyResult<PyObject> {
    let ty = normalize(py, ty)?;
    let b = ty.bind(py);
    if let Ok(tv) = b.downcast::<STypeVar>() {
        let tv_name = tv.borrow().name.clone_ref(py);
        if names_equal(py, &tv_name, &alpha) {
            return Ok(beta);
        }
        return Ok(ty);
    }
    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let rt = rt.borrow();
        let name = rt.name.clone_ref(py);
        let inner = rt.type_.clone_ref(py);
        let refinement = rt.refinement.clone_ref(py);
        let loc = rt.loc.clone_ref(py);
        drop(rt);
        let new_inner = substitute_svartype_in_stype(py, inner, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SRefinedType { name, type_: new_inner, refinement, loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(at) = b.downcast::<SAbstractionType>() {
        let at = at.borrow();
        let var_name = at.var_name.clone_ref(py);
        let var_type = at.var_type.clone_ref(py);
        let return_type = at.type_.clone_ref(py);
        let loc = at.loc.clone_ref(py);
        let mult = at.multiplicity.clone_ref(py);
        drop(at);
        let nv = substitute_svartype_in_stype(py, var_type, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nr = substitute_svartype_in_stype(py, return_type, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SAbstractionType {
                    var_name,
                    var_type: nv,
                    type_: nr,
                    loc,
                    multiplicity: mult,
                },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(tp) = b.downcast::<STypePolymorphism>() {
        let tp = tp.borrow();
        let name = tp.name.clone_ref(py);
        let kind = tp.kind.clone_ref(py);
        let body = tp.body.clone_ref(py);
        let loc = tp.loc.clone_ref(py);
        drop(tp);
        if names_equal(py, &name, &alpha) {
            return Ok(ty);
        }
        let nb = substitute_svartype_in_stype(py, body, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                STypePolymorphism { name, kind, body: nb, loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(rp) = b.downcast::<SRefinementPolymorphism>() {
        let rp = rp.borrow();
        let name = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        let loc = rp.loc.clone_ref(py);
        drop(rp);
        let ns = substitute_svartype_in_stype(py, sort, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nb = substitute_svartype_in_stype(py, body, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SRefinementPolymorphism { name, sort: ns, body: nb, loc },
                SType,
            ),
        )?
        .into_any());
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
            let arg = args_b.get_item(i)?.unbind();
            new_args.append(substitute_svartype_in_stype(
                py,
                arg,
                beta.clone_ref(py),
                alpha.clone_ref(py),
            )?)?;
        }
        return Ok(Py::new(
            py,
            (
                STypeConstructor { name, args: new_args.unbind(), loc },
                SType,
            ),
        )?
        .into_any());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unknown node in substitute {}",
        b.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn substitution_sterm_in_stype(
    py: Python<'_>,
    ty: PyObject,
    beta: PyObject,
    alpha: Py<Name>,
) -> PyResult<PyObject> {
    let b = ty.bind(py);
    if b.is_instance_of::<STypeVar>() {
        return Ok(ty);
    }
    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let rt = rt.borrow();
        let name = rt.name.clone_ref(py);
        let inner = rt.type_.clone_ref(py);
        let refinement = rt.refinement.clone_ref(py);
        let loc = rt.loc.clone_ref(py);
        drop(rt);
        let nt = substitution_sterm_in_stype(py, inner, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nref = substitution_sterm_in_sterm(py, refinement, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SRefinedType { name, type_: nt, refinement: nref, loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(at) = b.downcast::<SAbstractionType>() {
        let at = at.borrow();
        let var_name = at.var_name.clone_ref(py);
        let var_type = at.var_type.clone_ref(py);
        let return_type = at.type_.clone_ref(py);
        let loc = at.loc.clone_ref(py);
        let mult = at.multiplicity.clone_ref(py);
        drop(at);
        let nv = substitution_sterm_in_stype(py, var_type, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nr = substitution_sterm_in_stype(py, return_type, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SAbstractionType {
                    var_name,
                    var_type: nv,
                    type_: nr,
                    loc,
                    multiplicity: mult,
                },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(tp) = b.downcast::<STypePolymorphism>() {
        let tp = tp.borrow();
        let name = tp.name.clone_ref(py);
        let kind = tp.kind.clone_ref(py);
        let body = tp.body.clone_ref(py);
        let loc = tp.loc.clone_ref(py);
        drop(tp);
        let nb = substitution_sterm_in_stype(py, body, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                STypePolymorphism { name, kind, body: nb, loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(rp) = b.downcast::<SRefinementPolymorphism>() {
        let rp = rp.borrow();
        let name = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        let loc = rp.loc.clone_ref(py);
        drop(rp);
        if names_equal(py, &name, &alpha) {
            let ns = substitution_sterm_in_stype(py, sort, beta, alpha)?;
            return Ok(Py::new(
                py,
                (
                    SRefinementPolymorphism { name, sort: ns, body, loc },
                    SType,
                ),
            )?
            .into_any());
        }
        let ns = substitution_sterm_in_stype(py, sort, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nb = substitution_sterm_in_stype(py, body, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SRefinementPolymorphism { name, sort: ns, body: nb, loc },
                SType,
            ),
        )?
        .into_any());
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
            let arg = args_b.get_item(i)?.unbind();
            new_args.append(substitution_sterm_in_stype(
                py,
                arg,
                beta.clone_ref(py),
                alpha.clone_ref(py),
            )?)?;
        }
        return Ok(Py::new(
            py,
            (
                STypeConstructor { name, args: new_args.unbind(), loc },
                SType,
            ),
        )?
        .into_any());
    }
    // Fall through: unification var or other — return unchanged.
    Ok(ty)
}

#[pyfunction]
pub fn substitution_sterm_in_sterm(
    py: Python<'_>,
    t: PyObject,
    beta: PyObject,
    alpha: Py<Name>,
) -> PyResult<PyObject> {
    let b = t.bind(py);
    if b.is_instance_of::<SLiteral>()
        || b.is_instance_of::<SHole>()
        || b.is_instance_of::<SBy>()
        || b.is_instance_of::<SQualifiedVar>()
        || b.is_instance_of::<SAnonConstructor>()
    {
        return Ok(t);
    }
    if let Ok(v) = b.downcast::<SVar>() {
        let name = v.borrow().name.clone_ref(py);
        if names_equal(py, &name, &alpha) {
            return Ok(beta);
        }
        return Ok(t);
    }
    if let Ok(app) = b.downcast::<SApplication>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        let loc = app.loc.clone_ref(py);
        drop(app);
        let nfun = substitution_sterm_in_sterm(py, fun, beta.clone_ref(py), alpha.clone_ref(py))?;
        let narg = substitution_sterm_in_sterm(py, arg, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SApplication { fun: nfun, arg: narg, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ab) = b.downcast::<SAbstraction>() {
        let ab = ab.borrow();
        let aname = ab.var_name.clone_ref(py);
        let body = ab.body.clone_ref(py);
        let loc = ab.loc.clone_ref(py);
        drop(ab);
        if names_equal(py, &aname, &alpha) {
            return Ok(t);
        }
        let nb = substitution_sterm_in_sterm(py, body, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SAbstraction { var_name: aname, body: nb, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(le) = b.downcast::<SLet>() {
        let le = le.borrow();
        let vname = le.var_name.clone_ref(py);
        let vvalue = le.var_value.clone_ref(py);
        let body = le.body.clone_ref(py);
        let loc = le.loc.clone_ref(py);
        let mult = le.multiplicity.clone_ref(py);
        drop(le);
        let nv = substitution_sterm_in_sterm(py, vvalue, beta.clone_ref(py), alpha.clone_ref(py))?;
        if names_equal(py, &vname, &alpha) {
            return Ok(Py::new(
                py,
                (
                    SLet {
                        var_name: vname,
                        var_value: nv,
                        body,
                        loc,
                        multiplicity: mult,
                    },
                    STerm,
                ),
            )?
            .into_any());
        }
        let nb = substitution_sterm_in_sterm(py, body, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SLet {
                    var_name: vname,
                    var_value: nv,
                    body: nb,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(rc) = b.downcast::<SRec>() {
        let rc = rc.borrow();
        let vname = rc.var_name.clone_ref(py);
        let vty = rc.var_type.clone_ref(py);
        let vvalue = rc.var_value.clone_ref(py);
        let body = rc.body.clone_ref(py);
        let decreasing_by = rc.decreasing_by.clone_ref(py);
        let loc = rc.loc.clone_ref(py);
        let mult = rc.multiplicity.clone_ref(py);
        drop(rc);
        let nty = substitution_sterm_in_stype(py, vty, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nv = substitution_sterm_in_sterm(py, vvalue, beta.clone_ref(py), alpha.clone_ref(py))?;
        let dec_b = decreasing_by.bind(py);
        let nd_list = PyList::empty_bound(py);
        for i in 0..dec_b.len() {
            let item = dec_b.get_item(i)?.unbind();
            nd_list.append(substitution_sterm_in_sterm(
                py,
                item,
                beta.clone_ref(py),
                alpha.clone_ref(py),
            )?)?;
        }
        let nd_tuple = PyTuple::new_bound(py, nd_list.iter()).unbind();
        if names_equal(py, &vname, &alpha) {
            return Ok(Py::new(
                py,
                (
                    SRec {
                        var_name: vname,
                        var_type: nty,
                        var_value: nv,
                        body,
                        decreasing_by: nd_tuple,
                        loc,
                        multiplicity: mult,
                    },
                    STerm,
                ),
            )?
            .into_any());
        }
        let nb = substitution_sterm_in_sterm(py, body, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SRec {
                    var_name: vname,
                    var_type: nty,
                    var_value: nv,
                    body: nb,
                    decreasing_by: nd_tuple,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(an) = b.downcast::<SAnnotation>() {
        let an = an.borrow();
        let expr = an.expr.clone_ref(py);
        let ty = an.type_.clone_ref(py);
        let loc = an.loc.clone_ref(py);
        drop(an);
        let ne = substitution_sterm_in_sterm(py, expr, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nt = substitution_sterm_in_stype(py, ty, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SAnnotation { expr: ne, type_: nt, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ife) = b.downcast::<SIf>() {
        let ife = ife.borrow();
        let cond = ife.cond.clone_ref(py);
        let then = ife.then.clone_ref(py);
        let otherwise = ife.otherwise.clone_ref(py);
        let loc = ife.loc.clone_ref(py);
        drop(ife);
        let nc = substitution_sterm_in_sterm(py, cond, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nt = substitution_sterm_in_sterm(py, then, beta.clone_ref(py), alpha.clone_ref(py))?;
        let no = substitution_sterm_in_sterm(py, otherwise, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SIf { cond: nc, then: nt, otherwise: no, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(tap) = b.downcast::<STypeApplication>() {
        let tap = tap.borrow();
        let body = tap.body.clone_ref(py);
        let typ = tap.type_.clone_ref(py);
        let loc = tap.loc.clone_ref(py);
        drop(tap);
        let nb = substitution_sterm_in_sterm(py, body, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nt = substitution_sterm_in_stype(py, typ, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                STypeApplication { body: nb, type_: nt, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(rap) = b.downcast::<SRefinementApplication>() {
        let rap = rap.borrow();
        let body = rap.body.clone_ref(py);
        let refinement = rap.refinement.clone_ref(py);
        let loc = rap.loc.clone_ref(py);
        drop(rap);
        let nb = substitution_sterm_in_sterm(py, body, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nr = substitution_sterm_in_sterm(py, refinement, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SRefinementApplication { body: nb, refinement: nr, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ta) = b.downcast::<STypeAbstraction>() {
        let ta = ta.borrow();
        let name = ta.name.clone_ref(py);
        let kind = ta.kind.clone_ref(py);
        let body = ta.body.clone_ref(py);
        let loc = ta.loc.clone_ref(py);
        drop(ta);
        let nb = substitution_sterm_in_sterm(py, body, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                STypeAbstraction { name, kind, body: nb, loc },
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
        let ns = substitution_sterm_in_sterm(py, scrutinee, beta.clone_ref(py), alpha.clone_ref(py))?;
        let new_branches = PyList::empty_bound(py);
        let br_b = branches.bind(py);
        for i in 0..br_b.len() {
            let br_obj = br_b.get_item(i)?;
            let br = br_obj.downcast::<SMatchBranch>()?.borrow();
            let constructor = br.constructor.clone_ref(py);
            let binders = br.binders.clone_ref(py);
            let body = br.body.clone_ref(py);
            let qualifier = br.qualifier.clone();
            let br_loc = br.loc.clone_ref(py);
            drop(br);
            // If alpha is bound by branch binders, skip body substitution.
            let binders_b = binders.bind(py);
            let mut bound_here = false;
            for j in 0..binders_b.len() {
                let bn = binders_b.get_item(j)?;
                let bn_name: Py<Name> = bn.downcast::<Name>()?.clone().unbind();
                if names_equal(py, &bn_name, &alpha) {
                    bound_here = true;
                    break;
                }
            }
            let new_body = if bound_here {
                body
            } else {
                substitution_sterm_in_sterm(py, body, beta.clone_ref(py), alpha.clone_ref(py))?
            };
            new_branches.append(Py::new(
                py,
                SMatchBranch {
                    constructor,
                    binders,
                    body: new_body,
                    qualifier,
                    loc: br_loc,
                },
            )?)?;
        }
        return Ok(Py::new(
            py,
            (
                SMatch {
                    scrutinee: ns,
                    branches: new_branches.unbind(),
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if b.is_instance_of::<SMatchBranch>() {
        return Err(pyo3::exceptions::PyAssertionError::new_err(
            "SMatchBranch handled through SMatch",
        ));
    }
    if let Ok(ra) = b.downcast::<SRefinementAbstraction>() {
        let ra = ra.borrow();
        let pname = ra.name.clone_ref(py);
        let sort = ra.sort.clone_ref(py);
        let body = ra.body.clone_ref(py);
        let loc = ra.loc.clone_ref(py);
        drop(ra);
        if names_equal(py, &pname, &alpha) {
            return Ok(t);
        }
        let ns = substitution_sterm_in_stype(py, sort, beta.clone_ref(py), alpha.clone_ref(py))?;
        let nb = substitution_sterm_in_sterm(py, body, beta, alpha)?;
        return Ok(Py::new(
            py,
            (
                SRefinementAbstraction {
                    name: pname,
                    sort: ns,
                    body: nb,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unsupported term in substitution_sterm_in_sterm: {}",
        b.repr()?.to_string()
    )))
}

#[pyfunction]
pub fn substitute_refinement_param_in_stype(
    py: Python<'_>,
    ty: PyObject,
    old: Py<Name>,
    new: Py<Name>,
) -> PyResult<PyObject> {
    let ty = normalize(py, ty)?;
    let b = ty.bind(py);
    if b.is_instance_of::<STypeVar>() {
        return Ok(ty);
    }
    if let Ok(rt) = b.downcast::<SRefinedType>() {
        let rt = rt.borrow();
        let name = rt.name.clone_ref(py);
        let ity = rt.type_.clone_ref(py);
        let refinement = rt.refinement.clone_ref(py);
        let loc = rt.loc.clone_ref(py);
        drop(rt);
        let nity = substitute_refinement_param_in_stype(py, ity, old.clone_ref(py), new.clone_ref(py))?;
        let sv = Py::new(
            py,
            (
                SVar { name: new.clone_ref(py), loc: crate::loc::default_location(py) },
                STerm,
            ),
        )?
        .into_any();
        let nref = substitution_sterm_in_sterm(py, refinement, sv, old)?;
        return Ok(Py::new(
            py,
            (
                SRefinedType { name, type_: nity, refinement: nref, loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(at) = b.downcast::<SAbstractionType>() {
        let at = at.borrow();
        let var_name = at.var_name.clone_ref(py);
        let var_type = at.var_type.clone_ref(py);
        let return_type = at.type_.clone_ref(py);
        let loc = at.loc.clone_ref(py);
        let mult = at.multiplicity.clone_ref(py);
        drop(at);
        let nv = substitute_refinement_param_in_stype(py, var_type, old.clone_ref(py), new.clone_ref(py))?;
        let nr = substitute_refinement_param_in_stype(py, return_type, old, new)?;
        return Ok(Py::new(
            py,
            (
                SAbstractionType {
                    var_name,
                    var_type: nv,
                    type_: nr,
                    loc,
                    multiplicity: mult,
                },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(tp) = b.downcast::<STypePolymorphism>() {
        let tp = tp.borrow();
        let name = tp.name.clone_ref(py);
        let kind = tp.kind.clone_ref(py);
        let body = tp.body.clone_ref(py);
        let loc = tp.loc.clone_ref(py);
        drop(tp);
        let nb = substitute_refinement_param_in_stype(py, body, old, new)?;
        return Ok(Py::new(
            py,
            (
                STypePolymorphism { name, kind, body: nb, loc },
                SType,
            ),
        )?
        .into_any());
    }
    if let Ok(rp) = b.downcast::<SRefinementPolymorphism>() {
        let rp = rp.borrow();
        let name = rp.name.clone_ref(py);
        let sort = rp.sort.clone_ref(py);
        let body = rp.body.clone_ref(py);
        let loc = rp.loc.clone_ref(py);
        drop(rp);
        if names_equal(py, &name, &old) {
            return Ok(ty);
        }
        let ns = substitute_refinement_param_in_stype(py, sort, old.clone_ref(py), new.clone_ref(py))?;
        let nb = substitute_refinement_param_in_stype(py, body, old, new)?;
        return Ok(Py::new(
            py,
            (
                SRefinementPolymorphism { name, sort: ns, body: nb, loc },
                SType,
            ),
        )?
        .into_any());
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
            let arg = args_b.get_item(i)?.unbind();
            new_args.append(substitute_refinement_param_in_stype(
                py,
                arg,
                old.clone_ref(py),
                new.clone_ref(py),
            )?)?;
        }
        return Ok(Py::new(
            py,
            (
                STypeConstructor { name, args: new_args.unbind(), loc },
                SType,
            ),
        )?
        .into_any());
    }
    Ok(ty)
}

#[pyfunction]
pub fn substitution_svartype_in_sterm(
    py: Python<'_>,
    t: PyObject,
    rep: PyObject,
    name: Py<Name>,
) -> PyResult<PyObject> {
    let b = t.bind(py);
    if b.is_instance_of::<SVar>()
        || b.is_instance_of::<SHole>()
        || b.is_instance_of::<SBy>()
        || b.is_instance_of::<SQualifiedVar>()
        || b.is_instance_of::<SAnonConstructor>()
    {
        return Ok(t);
    }
    if let Ok(lit) = b.downcast::<SLiteral>() {
        let lit = lit.borrow();
        let value = lit.value.clone_ref(py);
        let ty = lit.type_.clone_ref(py);
        let loc = lit.loc.clone_ref(py);
        drop(lit);
        let nty = substitute_svartype_in_stype(py, ty, rep, name)?;
        return Ok(Py::new(
            py,
            (
                SLiteral { value, type_: nty, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(app) = b.downcast::<SApplication>() {
        let app = app.borrow();
        let fun = app.fun.clone_ref(py);
        let arg = app.arg.clone_ref(py);
        let loc = app.loc.clone_ref(py);
        drop(app);
        let nf = substitution_svartype_in_sterm(py, fun, rep.clone_ref(py), name.clone_ref(py))?;
        let na = substitution_svartype_in_sterm(py, arg, rep, name)?;
        return Ok(Py::new(
            py,
            (SApplication { fun: nf, arg: na, loc }, STerm),
        )?
        .into_any());
    }
    if let Ok(ab) = b.downcast::<SAbstraction>() {
        let ab = ab.borrow();
        let aname = ab.var_name.clone_ref(py);
        let body = ab.body.clone_ref(py);
        let loc = ab.loc.clone_ref(py);
        drop(ab);
        let nb = substitution_svartype_in_sterm(py, body, rep, name)?;
        return Ok(Py::new(
            py,
            (
                SAbstraction { var_name: aname, body: nb, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(le) = b.downcast::<SLet>() {
        let le = le.borrow();
        let vname = le.var_name.clone_ref(py);
        let vvalue = le.var_value.clone_ref(py);
        let body = le.body.clone_ref(py);
        let loc = le.loc.clone_ref(py);
        let mult = le.multiplicity.clone_ref(py);
        drop(le);
        let nv = substitution_svartype_in_sterm(py, vvalue, rep.clone_ref(py), name.clone_ref(py))?;
        let nb = substitution_svartype_in_sterm(py, body, rep, name)?;
        return Ok(Py::new(
            py,
            (
                SLet {
                    var_name: vname,
                    var_value: nv,
                    body: nb,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(rc) = b.downcast::<SRec>() {
        let rc = rc.borrow();
        let vname = rc.var_name.clone_ref(py);
        let vty = rc.var_type.clone_ref(py);
        let vvalue = rc.var_value.clone_ref(py);
        let body = rc.body.clone_ref(py);
        let decreasing_by = rc.decreasing_by.clone_ref(py);
        let loc = rc.loc.clone_ref(py);
        let mult = rc.multiplicity.clone_ref(py);
        drop(rc);
        let nty = substitute_svartype_in_stype(py, vty, rep.clone_ref(py), name.clone_ref(py))?;
        let nv = substitution_svartype_in_sterm(py, vvalue, rep.clone_ref(py), name.clone_ref(py))?;
        let nb = substitution_svartype_in_sterm(py, body, rep.clone_ref(py), name.clone_ref(py))?;
        let dec_b = decreasing_by.bind(py);
        let nd_list = PyList::empty_bound(py);
        for i in 0..dec_b.len() {
            let item = dec_b.get_item(i)?.unbind();
            nd_list.append(substitution_svartype_in_sterm(
                py,
                item,
                rep.clone_ref(py),
                name.clone_ref(py),
            )?)?;
        }
        let nd_tuple = PyTuple::new_bound(py, nd_list.iter()).unbind();
        return Ok(Py::new(
            py,
            (
                SRec {
                    var_name: vname,
                    var_type: nty,
                    var_value: nv,
                    body: nb,
                    decreasing_by: nd_tuple,
                    loc,
                    multiplicity: mult,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(an) = b.downcast::<SAnnotation>() {
        let an = an.borrow();
        let expr = an.expr.clone_ref(py);
        let ty = an.type_.clone_ref(py);
        let loc = an.loc.clone_ref(py);
        drop(an);
        let ne = substitution_svartype_in_sterm(py, expr, rep.clone_ref(py), name.clone_ref(py))?;
        let nt = substitute_svartype_in_stype(py, ty, rep, name)?;
        return Ok(Py::new(
            py,
            (
                SAnnotation { expr: ne, type_: nt, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ife) = b.downcast::<SIf>() {
        let ife = ife.borrow();
        let cond = ife.cond.clone_ref(py);
        let then = ife.then.clone_ref(py);
        let otherwise = ife.otherwise.clone_ref(py);
        let loc = ife.loc.clone_ref(py);
        drop(ife);
        let nc = substitution_svartype_in_sterm(py, cond, rep.clone_ref(py), name.clone_ref(py))?;
        let nt = substitution_svartype_in_sterm(py, then, rep.clone_ref(py), name.clone_ref(py))?;
        let no = substitution_svartype_in_sterm(py, otherwise, rep, name)?;
        return Ok(Py::new(
            py,
            (
                SIf { cond: nc, then: nt, otherwise: no, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(tap) = b.downcast::<STypeApplication>() {
        let tap = tap.borrow();
        let body = tap.body.clone_ref(py);
        let typ = tap.type_.clone_ref(py);
        let loc = tap.loc.clone_ref(py);
        drop(tap);
        let nb = substitution_svartype_in_sterm(py, body, rep.clone_ref(py), name.clone_ref(py))?;
        let nt = substitute_svartype_in_stype(py, typ, rep, name)?;
        return Ok(Py::new(
            py,
            (
                STypeApplication { body: nb, type_: nt, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(rap) = b.downcast::<SRefinementApplication>() {
        let rap = rap.borrow();
        let body = rap.body.clone_ref(py);
        let refinement = rap.refinement.clone_ref(py);
        let loc = rap.loc.clone_ref(py);
        drop(rap);
        let nb = substitution_svartype_in_sterm(py, body, rep.clone_ref(py), name.clone_ref(py))?;
        let nr = substitution_svartype_in_sterm(py, refinement, rep, name)?;
        return Ok(Py::new(
            py,
            (
                SRefinementApplication { body: nb, refinement: nr, loc },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ta) = b.downcast::<STypeAbstraction>() {
        let ta = ta.borrow();
        let aname = ta.name.clone_ref(py);
        let kind = ta.kind.clone_ref(py);
        let body = ta.body.clone_ref(py);
        let loc = ta.loc.clone_ref(py);
        drop(ta);
        if names_equal(py, &aname, &name) {
            return Ok(t);
        }
        let nb = substitution_svartype_in_sterm(py, body, rep, name)?;
        return Ok(Py::new(
            py,
            (
                STypeAbstraction { name: aname, kind, body: nb, loc },
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
        let ns = substitution_svartype_in_sterm(py, scrutinee, rep.clone_ref(py), name.clone_ref(py))?;
        let br_b = branches.bind(py);
        let new_branches = PyList::empty_bound(py);
        for i in 0..br_b.len() {
            let br_obj = br_b.get_item(i)?;
            let br = br_obj.downcast::<SMatchBranch>()?.borrow();
            let constructor = br.constructor.clone_ref(py);
            let binders = br.binders.clone_ref(py);
            let body = br.body.clone_ref(py);
            let qualifier = br.qualifier.clone();
            let br_loc = br.loc.clone_ref(py);
            drop(br);
            let nb = substitution_svartype_in_sterm(py, body, rep.clone_ref(py), name.clone_ref(py))?;
            new_branches.append(Py::new(
                py,
                SMatchBranch {
                    constructor,
                    binders,
                    body: nb,
                    qualifier,
                    loc: br_loc,
                },
            )?)?;
        }
        return Ok(Py::new(
            py,
            (
                SMatch {
                    scrutinee: ns,
                    branches: new_branches.unbind(),
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    if let Ok(ra) = b.downcast::<SRefinementAbstraction>() {
        let ra = ra.borrow();
        let pname = ra.name.clone_ref(py);
        let sort = ra.sort.clone_ref(py);
        let body = ra.body.clone_ref(py);
        let loc = ra.loc.clone_ref(py);
        drop(ra);
        let ns = substitute_svartype_in_stype(py, sort, rep.clone_ref(py), name.clone_ref(py))?;
        let nb = substitution_svartype_in_sterm(py, body, rep, name)?;
        return Ok(Py::new(
            py,
            (
                SRefinementAbstraction {
                    name: pname,
                    sort: ns,
                    body: nb,
                    loc,
                },
                STerm,
            ),
        )?
        .into_any());
    }
    Err(pyo3::exceptions::PyAssertionError::new_err(format!(
        "Unsupported term in substitution_svartype_in_sterm: {}",
        b.repr()?.to_string()
    )))
}

#[allow(dead_code)]
fn _silence() {
    let _ = get_multiplicity;
}
