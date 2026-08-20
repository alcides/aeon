//! Shared constructor helpers for the Aeon AST pyclasses.
//!
//! These build a `Py<...>` instance directly via `Py::new`, bypassing Python
//! attribute resolution (the `import_bound("aeon_rs").getattr(...)` path).
//! Used by the substitution / instantiation / liquefy walks.

use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::liquid::{
    LiquidApp, LiquidHornApplication, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt,
    LiquidLiteralString, LiquidTerm, LiquidVar,
};
use crate::name::Name;
use crate::terms::{
    Abstraction, Annotation, Application, If, Let, Literal, Rec, RefinementAbstraction,
    RefinementApplication, Term, TypeAbstraction, TypeApplication, Var,
};
use crate::types::{
    default_multiplicity, AbstractionType, ExistentialType, RefinedType, RefinementPolymorphism,
    Top, Type, TypeConstructor, TypePolymorphism, TypeVar,
};

#[inline]
pub fn name_eq(py: Python<'_>, a: &Py<Name>, b: &Py<Name>) -> bool {
    let a = a.borrow(py);
    let b = b.borrow(py);
    a.id == b.id && a.name == b.name
}

// -- Type constructors -------------------------------------------------------

pub fn new_top(py: Python<'_>) -> PyResult<PyObject> {
    Ok(Py::new(py, (Top { loc: crate::loc::default_location(py) }, Type))?.into_any())
}

pub fn new_type_var(py: Python<'_>, name: Py<Name>, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (TypeVar { name, loc }, Type))?.into_any())
}

pub fn new_refined_type(
    py: Python<'_>,
    name: Py<Name>,
    inner: PyObject,
    refinement: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (RefinedType { name, type_: inner, refinement, loc }, Type))?.into_any())
}

pub fn new_abstraction_type(
    py: Python<'_>,
    var_name: Py<Name>,
    var_type: PyObject,
    type_: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    let multiplicity = default_multiplicity(py);
    Ok(Py::new(
        py,
        (AbstractionType { var_name, var_type, type_, loc, multiplicity }, Type),
    )?
    .into_any())
}

pub fn new_abstraction_type_mult(
    py: Python<'_>,
    var_name: Py<Name>,
    var_type: PyObject,
    type_: PyObject,
    loc: PyObject,
    multiplicity: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(
        py,
        (AbstractionType { var_name, var_type, type_, loc, multiplicity }, Type),
    )?
    .into_any())
}

pub fn new_type_polymorphism(
    py: Python<'_>,
    name: Py<Name>,
    kind: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (TypePolymorphism { name, kind, body, loc }, Type))?.into_any())
}

pub fn new_refinement_polymorphism(
    py: Python<'_>,
    name: Py<Name>,
    sort: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (RefinementPolymorphism { name, sort, body, loc }, Type))?.into_any())
}

pub fn new_type_constructor(
    py: Python<'_>,
    name: Py<Name>,
    args: Py<PyList>,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (TypeConstructor { name, args, loc }, Type))?.into_any())
}

pub fn new_existential_type(
    py: Python<'_>,
    binders: Py<PyTuple>,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (ExistentialType { binders, body, loc }, Type))?.into_any())
}

// -- Term constructors -------------------------------------------------------

pub fn new_literal(py: Python<'_>, value: PyObject, type_: PyObject, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (Literal { value, type_, loc }, Term))?.into_any())
}

pub fn new_var(py: Python<'_>, name: Py<Name>, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (Var { name, loc }, Term))?.into_any())
}

pub fn new_application(py: Python<'_>, fun: PyObject, arg: PyObject, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (Application { fun, arg, loc }, Term))?.into_any())
}

pub fn new_abstraction(py: Python<'_>, var_name: Py<Name>, body: PyObject, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (Abstraction { var_name, body, loc }, Term))?.into_any())
}

pub fn new_let(
    py: Python<'_>,
    var_name: Py<Name>,
    var_value: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    let multiplicity = default_multiplicity(py);
    Ok(Py::new(
        py,
        (Let { var_name, var_value, body, loc, multiplicity }, Term),
    )?
    .into_any())
}

pub fn new_let_mult(
    py: Python<'_>,
    var_name: Py<Name>,
    var_value: PyObject,
    body: PyObject,
    loc: PyObject,
    multiplicity: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(
        py,
        (Let { var_name, var_value, body, loc, multiplicity }, Term),
    )?
    .into_any())
}

pub fn new_rec(
    py: Python<'_>,
    var_name: Py<Name>,
    var_type: PyObject,
    var_value: PyObject,
    body: PyObject,
    decreasing_by: Py<PyTuple>,
    loc: PyObject,
) -> PyResult<PyObject> {
    let multiplicity = default_multiplicity(py);
    Ok(Py::new(
        py,
        (
            Rec { var_name, var_type, var_value, body, decreasing_by, loc, multiplicity },
            Term,
        ),
    )?
    .into_any())
}

pub fn new_rec_mult(
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
            Rec { var_name, var_type, var_value, body, decreasing_by, loc, multiplicity },
            Term,
        ),
    )?
    .into_any())
}

pub fn new_annotation(py: Python<'_>, expr: PyObject, type_: PyObject, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (Annotation { expr, type_, loc }, Term))?.into_any())
}

pub fn new_if(
    py: Python<'_>,
    cond: PyObject,
    then: PyObject,
    otherwise: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (If { cond, then, otherwise, loc }, Term))?.into_any())
}

pub fn new_type_abstraction(
    py: Python<'_>,
    name: Py<Name>,
    kind: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (TypeAbstraction { name, kind, body, loc }, Term))?.into_any())
}

pub fn new_refinement_abstraction(
    py: Python<'_>,
    name: Py<Name>,
    sort: PyObject,
    body: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (RefinementAbstraction { name, sort, body, loc }, Term))?.into_any())
}

pub fn new_type_application(py: Python<'_>, body: PyObject, type_: PyObject, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (TypeApplication { body, type_, loc }, Term))?.into_any())
}

pub fn new_refinement_application(
    py: Python<'_>,
    body: PyObject,
    refinement: PyObject,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (RefinementApplication { body, refinement, loc }, Term))?.into_any())
}

// -- LiquidTerm constructors -------------------------------------------------

pub fn new_liquid_literal_bool(py: Python<'_>, value: bool, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (LiquidLiteralBool { value, loc }, LiquidTerm))?.into_any())
}

pub fn new_liquid_literal_int(py: Python<'_>, value: i64, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (LiquidLiteralInt { value, loc }, LiquidTerm))?.into_any())
}

pub fn new_liquid_literal_float(py: Python<'_>, value: f64, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (LiquidLiteralFloat { value, loc }, LiquidTerm))?.into_any())
}

pub fn new_liquid_literal_string(py: Python<'_>, value: String, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (LiquidLiteralString { value, loc }, LiquidTerm))?.into_any())
}

pub fn new_liquid_var(py: Python<'_>, name: Py<Name>, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (LiquidVar { name, loc }, LiquidTerm))?.into_any())
}

pub fn new_liquid_app(py: Python<'_>, fun: Py<Name>, args: Py<PyList>, loc: PyObject) -> PyResult<PyObject> {
    Ok(Py::new(py, (LiquidApp { fun, args, loc }, LiquidTerm))?.into_any())
}

pub fn new_liquid_horn_application(
    py: Python<'_>,
    name: Py<Name>,
    argtypes: Py<PyList>,
    loc: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (LiquidHornApplication { name, argtypes, loc }, LiquidTerm))?.into_any())
}

// -- Constraint constructors -------------------------------------------------

use crate::vcs::{
    Conjunction, Constraint, Implication, LiquidConstraint, ReflectedFunctionDeclaration,
    UninterpretedFunctionDeclaration,
};

pub fn new_liquid_constraint(
    py: Python<'_>,
    expr: PyObject,
    loc: Option<PyObject>,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (LiquidConstraint { expr, loc }, Constraint))?.into_any())
}

pub fn new_conjunction(
    py: Python<'_>,
    c1: PyObject,
    c2: PyObject,
    loc: Option<PyObject>,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (Conjunction { c1, c2, loc }, Constraint))?.into_any())
}

pub fn new_implication(
    py: Python<'_>,
    name: Py<Name>,
    base: PyObject,
    pred: PyObject,
    seq: PyObject,
    loc: Option<PyObject>,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (Implication { name, base, pred, seq, loc }, Constraint))?.into_any())
}

pub fn new_uninterpreted_function_declaration(
    py: Python<'_>,
    name: Py<Name>,
    type_: PyObject,
    seq: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(py, (UninterpretedFunctionDeclaration { name, type_, seq }, Constraint))?.into_any())
}

pub fn new_reflected_function_declaration(
    py: Python<'_>,
    name: Py<Name>,
    type_: PyObject,
    params: Py<PyTuple>,
    body: PyObject,
    seq: PyObject,
) -> PyResult<PyObject> {
    Ok(Py::new(
        py,
        (
            ReflectedFunctionDeclaration { name, type_, params, body, seq },
            Constraint,
        ),
    )?
    .into_any())
}
