//! Surface AST pretty-printer.
//! Port of `aeon.utils.pprint`.

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

use crate::name::Name;
use crate::pprint_helpers::{
    concat_docs, r_group, r_hard_line, r_insert_between, r_line, r_nest, r_nil, r_parens,
    r_soft_line, r_text, Doc, DEFAULT_TAB_SIZE, DEFAULT_WIDTH,
};
use crate::sugar::{
    Decorator, Definition, ImportAe, InductiveDecl, Program, SAbstraction, SAbstractionType,
    SAnnotation, SApplication, SBy, SHole, SIf, SLet, SLiteral, SQualifiedVar, SRec,
    SRefinedType, SRefinementAbstraction, STypeAbstraction, STypeApplication, STypeConstructor,
    STypePolymorphism, STypeVar, SVar, TypeDecl,
};

// ---------------------------------------------------------------------------
// Operation / Precedence / Associativity / Side
// ---------------------------------------------------------------------------

#[pyclass(module = "aeon_rs", eq, eq_int)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operation {
    INFIX_MULTIPLICATIVE = 1,
    INFIX_ADDITIVE = 2,
    INFIX_RELATIONAL = 3,
    INFIX_AND = 4,
    INFIX_OR = 5,
    POLYMORPHISM = 6,
    LET = 7,
    IF = 8,
    ARROW = 9,
    LAMBDA = 10,
    REFINED_TYPE = 11,
    ANNOTATION = 12,
    TYPE_CONSTRUCTOR = 13,
    APPLICATION = 14,
    TYPE_APPLICATION = 15,
    LITERAL = 16,
}

#[pyclass(module = "aeon_rs", eq, eq_int)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Precedence {
    POLYMORPHISM = 1,
    LET = 2,
    // IF shares value 2 with LET in the Python IntEnum.
    ANNOTATION = 3,
    ARROW = 4,
    LAMBDA = 5,
    REFINED_TYPE = 6,
    TYPE_CONSTRUCTOR = 7,
    INFIX_OR = 8,
    INFIX_AND = 9,
    INFIX_RELATIONAL = 10,
    INFIX_ADDITIVE = 11,
    INFIX_MULTIPLICATIVE = 12,
    APPLICATION = 13,
    TYPE_APPLICATION = 14,
    LITERAL = 15,
}

#[pymethods]
impl Precedence {
    #[classattr]
    #[allow(non_snake_case)]
    fn IF() -> Precedence {
        Precedence::LET
    }
}

#[pyclass(module = "aeon_rs", eq, eq_int)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Associativity {
    LEFT = 1,
    RIGHT = 2,
    NONE = 3,
}

#[pyclass(module = "aeon_rs", eq, eq_int)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Side {
    LEFT = 1,
    RIGHT = 2,
    NONE = 3,
}

fn get_operation_precedence(op: Operation) -> Precedence {
    match op {
        Operation::INFIX_MULTIPLICATIVE => Precedence::INFIX_MULTIPLICATIVE,
        Operation::INFIX_ADDITIVE => Precedence::INFIX_ADDITIVE,
        Operation::INFIX_RELATIONAL => Precedence::INFIX_RELATIONAL,
        Operation::INFIX_AND => Precedence::INFIX_AND,
        Operation::INFIX_OR => Precedence::INFIX_OR,
        Operation::POLYMORPHISM => Precedence::POLYMORPHISM,
        Operation::LET => Precedence::LET,
        Operation::IF => Precedence::LET, // shares value with LET
        Operation::ARROW => Precedence::ARROW,
        Operation::LAMBDA => Precedence::LAMBDA,
        Operation::REFINED_TYPE => Precedence::REFINED_TYPE,
        Operation::ANNOTATION => Precedence::ANNOTATION,
        Operation::TYPE_CONSTRUCTOR => Precedence::TYPE_CONSTRUCTOR,
        Operation::APPLICATION => Precedence::APPLICATION,
        Operation::TYPE_APPLICATION => Precedence::TYPE_APPLICATION,
        Operation::LITERAL => Precedence::LITERAL,
    }
}

fn get_operation_associativity(op: Operation) -> Associativity {
    match op {
        Operation::ARROW => Associativity::RIGHT,
        Operation::LAMBDA => Associativity::RIGHT,
        Operation::INFIX_MULTIPLICATIVE
        | Operation::INFIX_ADDITIVE
        | Operation::INFIX_AND
        | Operation::INFIX_OR
        | Operation::APPLICATION
        | Operation::TYPE_APPLICATION => Associativity::LEFT,
        _ => Associativity::NONE,
    }
}

#[pyclass(module = "aeon_rs", frozen)]
#[derive(Clone)]
pub struct ParenthesisContext {
    #[pyo3(get)]
    pub parent_precedence: Precedence,
    #[pyo3(get)]
    pub child_side: Side,
}

#[pymethods]
impl ParenthesisContext {
    #[new]
    fn py_new(parent_precedence: Precedence, child_side: Side) -> Self {
        ParenthesisContext { parent_precedence, child_side }
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        match other.downcast::<ParenthesisContext>() {
            Ok(o) => {
                let o = o.borrow();
                self.parent_precedence == o.parent_precedence && self.child_side == o.child_side
            }
            Err(_) => false,
        }
    }

    fn __hash__(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        (self.parent_precedence as u8).hash(&mut h);
        (self.child_side as u8).hash(&mut h);
        h.finish()
    }
}

const INFIX_MULTIPLICATIVE: &[&str] = &["*", "/", "%", "*.", "/.", "%."];
const INFIX_ADDITIVE: &[&str] = &["+", "-", "+.", "-."];
const INFIX_RELATIONAL: &[&str] = &["<", "<=", ">", ">=", "==", "!="];
const INFIX_AND: &[&str] = &["&&"];
const INFIX_OR: &[&str] = &["||"];

fn is_infix_op(s: &str) -> bool {
    INFIX_MULTIPLICATIVE.contains(&s)
        || INFIX_ADDITIVE.contains(&s)
        || INFIX_RELATIONAL.contains(&s)
        || INFIX_AND.contains(&s)
        || INFIX_OR.contains(&s)
}

fn get_infix_op_for(s: &str) -> Operation {
    if INFIX_MULTIPLICATIVE.contains(&s) {
        Operation::INFIX_MULTIPLICATIVE
    } else if INFIX_ADDITIVE.contains(&s) {
        Operation::INFIX_ADDITIVE
    } else if INFIX_RELATIONAL.contains(&s) {
        Operation::INFIX_RELATIONAL
    } else if INFIX_AND.contains(&s) {
        Operation::INFIX_AND
    } else {
        // INFIX_OR or fallback (Python returns INFIX_OR in else)
        Operation::INFIX_OR
    }
}

// ---------------------------------------------------------------------------
// Helpers: get_sterm_operation, get_stype_operation, needs_parens
// ---------------------------------------------------------------------------

/// Detects `SApplication(SApplication(SVar(name=op), left), right)` where op
/// is an infix operator. Returns (op_name, left, right) on match.
fn detect_infix(
    py: Python<'_>,
    sterm: &Bound<'_, PyAny>,
) -> PyResult<Option<(String, PyObject, PyObject)>> {
    let Ok(outer) = sterm.downcast::<SApplication>() else {
        return Ok(None);
    };
    let outer_b = outer.borrow();
    let fun = outer_b.fun.clone_ref(py);
    let right = outer_b.arg.clone_ref(py);
    drop(outer_b);
    let fun_b = fun.bind(py);
    let Ok(inner) = fun_b.downcast::<SApplication>() else {
        return Ok(None);
    };
    let inner_b = inner.borrow();
    let inner_fun = inner_b.fun.clone_ref(py);
    let left = inner_b.arg.clone_ref(py);
    drop(inner_b);
    let inner_fun_b = inner_fun.bind(py);
    let Ok(v) = inner_fun_b.downcast::<SVar>() else {
        return Ok(None);
    };
    let v = v.borrow();
    let op = v.name.borrow(py).pretty();
    drop(v);
    if is_infix_op(&op) {
        Ok(Some((op, left, right)))
    } else {
        Ok(None)
    }
}

/// Also handles the type-applied form:
/// `SApplication(SApplication(STypeApplication(SVar(op), _), left), right)`.
fn detect_infix_with_typeapp(
    py: Python<'_>,
    sterm: &Bound<'_, PyAny>,
) -> PyResult<Option<(String, PyObject, PyObject)>> {
    if let Some(hit) = detect_infix(py, sterm)? {
        return Ok(Some(hit));
    }
    let Ok(outer) = sterm.downcast::<SApplication>() else {
        return Ok(None);
    };
    let outer_b = outer.borrow();
    let fun = outer_b.fun.clone_ref(py);
    let right = outer_b.arg.clone_ref(py);
    drop(outer_b);
    let fun_b = fun.bind(py);
    let Ok(inner) = fun_b.downcast::<SApplication>() else {
        return Ok(None);
    };
    let inner_b = inner.borrow();
    let inner_fun = inner_b.fun.clone_ref(py);
    let left = inner_b.arg.clone_ref(py);
    drop(inner_b);
    let inner_fun_b = inner_fun.bind(py);
    let Ok(tap) = inner_fun_b.downcast::<STypeApplication>() else {
        return Ok(None);
    };
    let tap_b = tap.borrow();
    let body = tap_b.body.clone_ref(py);
    drop(tap_b);
    let body_b = body.bind(py);
    let Ok(v) = body_b.downcast::<SVar>() else {
        return Ok(None);
    };
    let v = v.borrow();
    let op = v.name.borrow(py).pretty();
    drop(v);
    if is_infix_op(&op) {
        Ok(Some((op, left, right)))
    } else {
        Ok(None)
    }
}

fn get_sterm_operation(py: Python<'_>, sterm: &Bound<'_, PyAny>) -> PyResult<Operation> {
    if sterm.downcast::<SLet>().is_ok() {
        return Ok(Operation::LET);
    }
    if sterm.downcast::<SIf>().is_ok() {
        return Ok(Operation::IF);
    }
    if sterm.downcast::<SAbstraction>().is_ok() {
        return Ok(Operation::LAMBDA);
    }
    if let Some((op, _, _)) = detect_infix(py, sterm)? {
        return Ok(get_infix_op_for(&op));
    }
    if sterm.downcast::<SApplication>().is_ok() {
        return Ok(Operation::APPLICATION);
    }
    if sterm.downcast::<SAnnotation>().is_ok() {
        return Ok(Operation::ANNOTATION);
    }
    if sterm.downcast::<SRec>().is_ok() {
        return Ok(Operation::LET);
    }
    if sterm.downcast::<STypeAbstraction>().is_ok() {
        return Ok(Operation::POLYMORPHISM);
    }
    if sterm.downcast::<SRefinementAbstraction>().is_ok() {
        return Ok(Operation::POLYMORPHISM);
    }
    if sterm.downcast::<STypeApplication>().is_ok() {
        return Ok(Operation::TYPE_APPLICATION);
    }
    Ok(Operation::LITERAL)
}

fn get_stype_operation(stype: &Bound<'_, PyAny>) -> Operation {
    if stype.downcast::<STypeVar>().is_ok() {
        return Operation::LITERAL;
    }
    if stype.downcast::<SRefinedType>().is_ok() {
        return Operation::REFINED_TYPE;
    }
    if stype.downcast::<SAbstractionType>().is_ok() {
        return Operation::ARROW;
    }
    if stype.downcast::<STypePolymorphism>().is_ok() {
        return Operation::POLYMORPHISM;
    }
    if stype.downcast::<STypeConstructor>().is_ok() {
        return Operation::TYPE_CONSTRUCTOR;
    }
    Operation::LITERAL
}

fn needs_parens_internal(child_op: Operation, ctx: &ParenthesisContext) -> bool {
    let child_prec = get_operation_precedence(child_op);
    let parent_prec = ctx.parent_precedence;
    let child_side = ctx.child_side;
    let child_assoc = get_operation_associativity(child_op);
    needs_parens_aux_internal(child_assoc, child_prec, child_side, parent_prec)
}

fn needs_parens_aux_internal(
    child_associativity: Associativity,
    child_precedence: Precedence,
    child_side: Side,
    parent_precedence: Precedence,
) -> bool {
    if (child_precedence as u8) < (parent_precedence as u8) {
        return true;
    }
    if (child_precedence as u8) > (parent_precedence as u8) {
        return false;
    }
    if matches!(child_associativity, Associativity::NONE) {
        return false;
    }
    if matches!(child_associativity, Associativity::LEFT) && matches!(child_side, Side::RIGHT) {
        return true;
    }
    if matches!(child_associativity, Associativity::RIGHT) && matches!(child_side, Side::LEFT) {
        return true;
    }
    false
}

fn add_parens_if_needed(doc: Doc, child_op: Operation, ctx: &ParenthesisContext) -> Doc {
    if needs_parens_internal(child_op, ctx) {
        r_parens(&doc, false)
    } else {
        doc
    }
}

// ---------------------------------------------------------------------------
// Recursive pretty-printers
// ---------------------------------------------------------------------------

fn pretty_stype_with_parens(
    py: Python<'_>,
    stype: &Bound<'_, PyAny>,
    ctx: &ParenthesisContext,
) -> PyResult<Doc> {
    let child_op = get_stype_operation(stype);
    let new_ctx = ParenthesisContext {
        parent_precedence: get_operation_precedence(child_op),
        child_side: Side::NONE,
    };
    let child = stype_pretty_internal(py, stype, &new_ctx)?;
    Ok(add_parens_if_needed(child, child_op, ctx))
}

fn pretty_sterm_with_parens(
    py: Python<'_>,
    sterm: &Bound<'_, PyAny>,
    ctx: &ParenthesisContext,
    depth: i64,
) -> PyResult<Doc> {
    let child_op = get_sterm_operation(py, sterm)?;
    let new_ctx = ParenthesisContext {
        parent_precedence: get_operation_precedence(child_op),
        child_side: Side::NONE,
    };
    let child = sterm_pretty_internal(py, sterm, &new_ctx, depth)?;
    Ok(add_parens_if_needed(child, child_op, ctx))
}

fn format_infix_application(
    py: Python<'_>,
    left: &Bound<'_, PyAny>,
    right: &Bound<'_, PyAny>,
    op: &str,
    depth: i64,
) -> PyResult<Doc> {
    let infix_op = get_infix_op_for(op);
    let infix_prec = get_operation_precedence(infix_op);
    let left_ctx = ParenthesisContext { parent_precedence: infix_prec, child_side: Side::LEFT };
    let right_ctx = ParenthesisContext { parent_precedence: infix_prec, child_side: Side::RIGHT };
    let pl = pretty_sterm_with_parens(py, left, &left_ctx, depth + 1)?;
    let pr = pretty_sterm_with_parens(py, right, &right_ctx, depth + 1)?;
    Ok(r_group(&concat_docs(&[pl, r_line(), r_text(op), r_line(), pr])))
}

fn pretty_param_doc(
    py: Python<'_>,
    param_name: &Py<Name>,
    param_type: &Bound<'_, PyAny>,
) -> PyResult<Doc> {
    if let Ok(rt) = param_type.downcast::<SRefinedType>() {
        let rt_b = rt.borrow();
        let ref_name = rt_b.name.clone_ref(py);
        let ref_type = rt_b.type_.clone_ref(py);
        let refinement = rt_b.refinement.clone_ref(py);
        drop(rt_b);
        let ref_name_str = ref_name.borrow(py).pretty();
        let param_name_str = param_name.borrow(py).pretty();
        if ref_name_str == param_name_str {
            let type_doc = stype_pretty_internal(
                py,
                ref_type.bind(py),
                &ParenthesisContext {
                    parent_precedence: Precedence::LITERAL,
                    child_side: Side::NONE,
                },
            )?;
            let refinement_doc = sterm_pretty_internal(
                py,
                refinement.bind(py),
                &ParenthesisContext {
                    parent_precedence: Precedence::REFINED_TYPE,
                    child_side: Side::RIGHT,
                },
                1,
            )?;
            let inner = concat_docs(&[
                r_text(&ref_name_str),
                r_text(" : "),
                type_doc,
                r_text(" | "),
                refinement_doc,
            ]);
            return Ok(r_parens(&inner, false));
        }
    }
    let param_name_str = param_name.borrow(py).pretty();
    let type_doc = stype_pretty_internal(
        py,
        param_type,
        &ParenthesisContext { parent_precedence: Precedence::LITERAL, child_side: Side::NONE },
    )?;
    let inner = concat_docs(&[r_text(&param_name_str), r_text(" : "), type_doc]);
    Ok(r_parens(&inner, false))
}

fn pretty_print_function_definition(
    py: Python<'_>,
    func_name_doc: &Doc,
    params: &[(Py<Name>, PyObject)],
    return_type: &Bound<'_, PyAny>,
) -> PyResult<(Doc, i64)> {
    let (first_name, first_type) = &params[0];
    let first_param_doc = pretty_param_doc(py, first_name, first_type.bind(py))?;
    let func_header = concat_docs(&[
        r_text("def "),
        func_name_doc.clone(),
        r_text(" "),
        first_param_doc,
    ]);

    let func_name_layout = func_name_doc.layout(0);
    let indent_after_first =
        ("def ".len() as i64) + (func_name_layout.chars().count() as i64) + 1;

    let mut additional = r_nil();
    for (pname, ptype) in &params[1..] {
        let pd = pretty_param_doc(py, pname, ptype.bind(py))?;
        additional = concat_docs(&[additional, r_line(), pd]);
    }
    let rt_doc = stype_pretty_internal(
        py,
        return_type,
        &ParenthesisContext { parent_precedence: Precedence::LITERAL, child_side: Side::NONE },
    )?;
    let nest_body = concat_docs(&[additional, r_line(), r_text(": "), rt_doc]);
    let full = concat_docs(&[func_header, r_nest(indent_after_first, &nest_body)]);
    Ok((full, indent_after_first))
}

fn unwrap_abstraction_types(
    py: Python<'_>,
    stype: PyObject,
) -> PyResult<(Vec<(Py<Name>, PyObject)>, PyObject)> {
    let mut named: Vec<(Py<Name>, PyObject)> = Vec::new();
    let mut curr = stype;
    loop {
        let b = curr.bind(py);
        if let Ok(at) = b.downcast::<SAbstractionType>() {
            let at_b = at.borrow();
            let vn = at_b.var_name.clone_ref(py);
            let vt = at_b.var_type.clone_ref(py);
            let next = at_b.type_.clone_ref(py);
            drop(at_b);
            named.push((vn, vt));
            curr = next;
        } else {
            return Ok((named, curr));
        }
    }
}

fn strip_matching_abstractions(
    py: Python<'_>,
    abstraction: PyObject,
    arguments: &[(Py<Name>, PyObject)],
) -> PyResult<PyObject> {
    let mut stripped = abstraction;
    for (arg_name, _) in arguments {
        let stripped_b = stripped.bind(py);
        if let Ok(abs) = stripped_b.downcast::<SAbstraction>() {
            let abs_b = abs.borrow();
            let vn_name = {
                let vn = abs_b.var_name.borrow(py);
                vn.name.clone()
            };
            let arg_name_s = arg_name.borrow(py).name.clone();
            if vn_name == arg_name_s {
                let body = abs_b.body.clone_ref(py);
                drop(abs_b);
                stripped = body;
                continue;
            }
        }
        break;
    }
    Ok(stripped)
}

// ---- stype_pretty -------------------------------------------------------

fn stype_pretty_internal(
    py: Python<'_>,
    stype: &Bound<'_, PyAny>,
    ctx: &ParenthesisContext,
) -> PyResult<Doc> {
    if let Ok(tv) = stype.downcast::<STypeVar>() {
        let tv_b = tv.borrow();
        let n = tv_b.name.borrow(py).pretty();
        return Ok(r_text(&n));
    }
    if let Ok(rt) = stype.downcast::<SRefinedType>() {
        let rt_b = rt.borrow();
        let name = rt_b.name.clone_ref(py);
        let type_ = rt_b.type_.clone_ref(py);
        let refinement = rt_b.refinement.clone_ref(py);
        drop(rt_b);
        let pretty_name = r_text(&name.borrow(py).pretty());
        let type_doc = pretty_stype_with_parens(
            py,
            type_.bind(py),
            &ParenthesisContext {
                parent_precedence: Precedence::REFINED_TYPE,
                child_side: Side::RIGHT,
            },
        )?;
        let refinement_doc = pretty_sterm_with_parens(
            py,
            refinement.bind(py),
            &ParenthesisContext {
                parent_precedence: Precedence::REFINED_TYPE,
                child_side: Side::RIGHT,
            },
            1,
        )?;
        let pair = concat_docs(&[pretty_name, r_text(" : "), type_doc]);
        let inner = concat_docs(&[r_soft_line(), pair, r_text(" | "), refinement_doc]);
        let nested = r_nest(DEFAULT_WIDTH, &inner);
        let _ = ctx;
        return Ok(r_group(&concat_docs(&[
            r_text("{"),
            nested,
            r_soft_line(),
            r_text("}"),
        ])));
    }
    if let Ok(at) = stype.downcast::<SAbstractionType>() {
        let at_b = at.borrow();
        let var_name = at_b.var_name.clone_ref(py);
        let var_type = at_b.var_type.clone_ref(py);
        let inner_type = at_b.type_.clone_ref(py);
        drop(at_b);
        let pretty_var_name = r_text(&var_name.borrow(py).pretty());
        let vt_doc = pretty_stype_with_parens(
            py,
            var_type.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::ANNOTATION, child_side: Side::RIGHT },
        )?;
        let mut left_doc =
            concat_docs(&[pretty_var_name, r_text(" : "), vt_doc]);
        left_doc = add_parens_if_needed(
            left_doc,
            Operation::ANNOTATION,
            &ParenthesisContext { parent_precedence: Precedence::ARROW, child_side: Side::LEFT },
        );
        let right_doc = pretty_stype_with_parens(
            py,
            inner_type.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::ARROW, child_side: Side::RIGHT },
        )?;
        let _ = ctx;
        return Ok(r_group(&concat_docs(&[
            left_doc,
            r_text(" ->"),
            r_line(),
            right_doc,
        ])));
    }
    if let Ok(tp) = stype.downcast::<STypePolymorphism>() {
        let tp_b = tp.borrow();
        let name = tp_b.name.clone_ref(py);
        let kind = tp_b.kind.clone_ref(py);
        let body = tp_b.body.clone_ref(py);
        drop(tp_b);
        let pretty_name = r_text(&name.borrow(py).pretty());
        let kind_str = kind.bind(py).str()?.to_string();
        let pretty_kind = r_text(&kind_str);
        let pretty_body = pretty_stype_with_parens(
            py,
            body.bind(py),
            &ParenthesisContext {
                parent_precedence: Precedence::POLYMORPHISM,
                child_side: Side::RIGHT,
            },
        )?;
        let left = concat_docs(&[r_text("∀"), pretty_name, r_text(" : "), pretty_kind]);
        let body_inner = concat_docs(&[r_line(), pretty_body]);
        let _ = ctx;
        return Ok(r_group(&concat_docs(&[
            left,
            r_text(" ."),
            r_nest(DEFAULT_TAB_SIZE, &body_inner),
        ])));
    }
    if let Ok(tc) = stype.downcast::<STypeConstructor>() {
        let tc_b = tc.borrow();
        let name = tc_b.name.clone_ref(py);
        let args = tc_b.args.clone_ref(py);
        drop(tc_b);
        let pretty_name = r_text(&name.borrow(py).pretty());
        let args_b = args.bind(py);
        if args_b.is_empty() {
            return Ok(pretty_name);
        }
        let mut pretty_args: Vec<Doc> = Vec::with_capacity(args_b.len());
        for i in 0..args_b.len() {
            let arg = args_b.get_item(i)?;
            let d = pretty_stype_with_parens(
                py,
                &arg,
                &ParenthesisContext {
                    parent_precedence: Precedence::TYPE_CONSTRUCTOR,
                    child_side: Side::RIGHT,
                },
            )?;
            pretty_args.push(d);
        }
        let args_doc = r_insert_between(&r_text(" "), &pretty_args);
        let _ = ctx;
        return Ok(r_group(&concat_docs(&[pretty_name, r_text(" "), args_doc])));
    }
    // Fallback: str(stype)
    Ok(r_text(&stype.str()?.to_string()))
}

// ---- sterm_pretty -------------------------------------------------------

fn sterm_pretty_internal(
    py: Python<'_>,
    sterm: &Bound<'_, PyAny>,
    ctx: &ParenthesisContext,
    depth: i64,
) -> PyResult<Doc> {
    // SLiteral
    if let Ok(lit) = sterm.downcast::<SLiteral>() {
        let lit_b = lit.borrow();
        let value = lit_b.value.clone_ref(py);
        let type_ = lit_b.type_.clone_ref(py);
        drop(lit_b);
        let is_string = if let Ok(tc) = type_.bind(py).downcast::<STypeConstructor>() {
            let tc_b = tc.borrow();
            let n = tc_b.name.borrow(py);
            n.id == 0 && n.name == "String" && tc_b.args.bind(py).len() == 0
        } else {
            false
        };
        if is_string {
            return Ok(r_text(&format!("\"{}\"", value.bind(py).str()?)));
        }
        return Ok(r_text(&value.bind(py).str()?.to_string()));
    }
    // SVar
    if let Ok(v) = sterm.downcast::<SVar>() {
        let v_b = v.borrow();
        let n = v_b.name.borrow(py).pretty();
        return Ok(r_text(&n));
    }
    // SQualifiedVar
    if let Ok(qv) = sterm.downcast::<SQualifiedVar>() {
        let qv_b = qv.borrow();
        let qualifier = qv_b.qualifier.clone();
        let n = qv_b.name.borrow(py).pretty();
        return Ok(r_text(&format!("{}.{}", qualifier, n)));
    }
    // SHole
    if let Ok(h) = sterm.downcast::<SHole>() {
        let h_b = h.borrow();
        let n = h_b.name.borrow(py).pretty();
        return Ok(r_text(&format!("?{}", n)));
    }
    // SBy
    if let Ok(by) = sterm.downcast::<SBy>() {
        let by_b = by.borrow();
        let steps = by_b.steps.bind(py);
        let mut parts: Vec<String> = Vec::with_capacity(steps.len());
        for i in 0..steps.len() {
            let item = steps.get_item(i)?;
            parts.push(item.str()?.to_string());
        }
        let inner = r_text(&parts.join("; "));
        return Ok(r_group(&concat_docs(&[r_text("by "), inner])));
    }
    // SAnnotation
    if let Ok(ann) = sterm.downcast::<SAnnotation>() {
        let ann_b = ann.borrow();
        let expr = ann_b.expr.clone_ref(py);
        let type_ = ann_b.type_.clone_ref(py);
        drop(ann_b);
        let expr_doc = pretty_sterm_with_parens(
            py,
            expr.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::ANNOTATION, child_side: Side::LEFT },
            depth + 1,
        )?;
        let type_doc = stype_pretty_internal(
            py,
            type_.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::ANNOTATION, child_side: Side::RIGHT },
        )?;
        let _ = ctx;
        let nest_body = concat_docs(&[r_line(), type_doc]);
        return Ok(r_group(&concat_docs(&[
            expr_doc,
            r_text(" :"),
            r_nest(DEFAULT_TAB_SIZE, &nest_body),
        ])));
    }
    // SIf
    if let Ok(iff) = sterm.downcast::<SIf>() {
        let iff_b = iff.borrow();
        let cond = iff_b.cond.clone_ref(py);
        let then = iff_b.then.clone_ref(py);
        let otherwise = iff_b.otherwise.clone_ref(py);
        drop(iff_b);
        let cond_doc = pretty_sterm_with_parens(
            py,
            cond.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::LET, child_side: Side::NONE },
            depth + 1,
        )?;
        let then_doc = pretty_sterm_with_parens(
            py,
            then.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::LET, child_side: Side::NONE },
            depth + 1,
        )?;
        let otherwise_doc = pretty_sterm_with_parens(
            py,
            otherwise.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::LET, child_side: Side::NONE },
            depth + 1,
        )?;
        let _ = ctx;
        return Ok(r_group(&concat_docs(&[
            r_text("if "),
            cond_doc,
            r_line(),
            r_text("then "),
            r_nest(DEFAULT_TAB_SIZE, &then_doc),
            r_line(),
            r_text("else "),
            r_nest(DEFAULT_TAB_SIZE, &otherwise_doc),
        ])));
    }
    // SApplication (infix handling, main filtering, then plain)
    if let Ok(app) = sterm.downcast::<SApplication>() {
        // Infix forms — both plain and type-applied
        if let Some((op, left, right)) = detect_infix_with_typeapp(py, sterm)? {
            return format_infix_application(py, left.bind(py), right.bind(py), &op, depth);
        }
        let app_b = app.borrow();
        let fun = app_b.fun.clone_ref(py);
        let arg = app_b.arg.clone_ref(py);
        drop(app_b);

        // Skip top-level `main` application at depth 0.
        if depth == 0 {
            let fun_b = fun.bind(py);
            if let Ok(v) = fun_b.downcast::<SVar>() {
                let v_b = v.borrow();
                let nm = v_b.name.borrow(py).pretty();
                if nm == "main" {
                    return Ok(r_nil());
                }
            }
        }
        let fun_doc = pretty_sterm_with_parens(
            py,
            fun.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::APPLICATION, child_side: Side::LEFT },
            depth + 1,
        )?;
        let arg_doc = pretty_sterm_with_parens(
            py,
            arg.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::APPLICATION, child_side: Side::RIGHT },
            depth + 1,
        )?;
        let _ = ctx;
        return Ok(r_group(&concat_docs(&[fun_doc, r_line(), arg_doc])));
    }
    // SAbstraction
    if let Ok(abs) = sterm.downcast::<SAbstraction>() {
        let abs_b = abs.borrow();
        let var_name = abs_b.var_name.clone_ref(py);
        let body = abs_b.body.clone_ref(py);
        drop(abs_b);
        let pretty_var_name = r_text(&var_name.borrow(py).pretty());
        let left = concat_docs(&[r_text("\\"), pretty_var_name, r_text(" ->")]);
        let body_doc = pretty_sterm_with_parens(
            py,
            body.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::ARROW, child_side: Side::RIGHT },
            depth + 1,
        )?;
        let _ = ctx;
        let body_inner = concat_docs(&[r_line(), body_doc]);
        return Ok(r_group(&concat_docs(&[left, r_nest(DEFAULT_TAB_SIZE, &body_inner)])));
    }
    // SLet
    if let Ok(lt) = sterm.downcast::<SLet>() {
        let lt_b = lt.borrow();
        let var_name = lt_b.var_name.clone_ref(py);
        let var_value = lt_b.var_value.clone_ref(py);
        let body = lt_b.body.clone_ref(py);
        drop(lt_b);
        let pretty_var_name = r_text(&var_name.borrow(py).pretty());
        let pretty_var_value = pretty_sterm_with_parens(
            py,
            var_value.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::LET, child_side: Side::NONE },
            depth + 1,
        )?;
        let pretty_body = pretty_sterm_with_parens(
            py,
            body.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::LET, child_side: Side::NONE },
            depth,
        )?;
        let _ = ctx;
        if depth == 0 {
            let inner = concat_docs(&[r_line(), pretty_var_value]);
            return Ok(r_group(&concat_docs(&[
                r_text("def "),
                pretty_var_name,
                r_text(" ="),
                r_nest(DEFAULT_TAB_SIZE, &inner),
                r_hard_line(),
                r_hard_line(),
                pretty_body,
            ])));
        } else {
            let binding = concat_docs(&[pretty_var_name, r_text(" = "), pretty_var_value]);
            return Ok(r_group(&concat_docs(&[
                r_text("let "),
                binding,
                r_text(" in"),
                r_line(),
                pretty_body,
            ])));
        }
    }
    // SRec
    if let Ok(rec) = sterm.downcast::<SRec>() {
        let rec_b = rec.borrow();
        let var_name = rec_b.var_name.clone_ref(py);
        let var_type = rec_b.var_type.clone_ref(py);
        let var_value = rec_b.var_value.clone_ref(py);
        let body = rec_b.body.clone_ref(py);
        drop(rec_b);
        let pretty_var_name = r_text(&var_name.borrow(py).pretty());
        let pretty_var_type = pretty_stype_with_parens(
            py,
            var_type.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::ANNOTATION, child_side: Side::RIGHT },
        )?;
        let pretty_var_value = pretty_sterm_with_parens(
            py,
            var_value.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::LET, child_side: Side::NONE },
            depth + 1,
        )?;
        let pretty_body = pretty_sterm_with_parens(
            py,
            body.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::LET, child_side: Side::NONE },
            depth,
        )?;
        let _ = ctx;
        if depth != 0 {
            let binding = concat_docs(&[
                pretty_var_name,
                r_text(" : "),
                pretty_var_type,
                r_text(" = "),
                pretty_var_value,
            ]);
            return Ok(r_group(&concat_docs(&[
                r_text("let "),
                binding,
                r_text(" in"),
                r_line(),
                pretty_body,
            ])));
        }
        // depth == 0
        let full_type = if var_type.bind(py).downcast::<SAbstractionType>().is_ok() {
            let (named_vars, final_type) = unwrap_abstraction_types(py, var_type.clone_ref(py))?;
            let (pretty_func_def, _alignment) =
                pretty_print_function_definition(py, &pretty_var_name, &named_vars, final_type.bind(py))?;
            let stripped_value =
                strip_matching_abstractions(py, var_value.clone_ref(py), &named_vars)?;
            let pretty_var_value2 = pretty_sterm_with_parens(
                py,
                stripped_value.bind(py),
                &ParenthesisContext { parent_precedence: Precedence::LET, child_side: Side::NONE },
                depth + 1,
            )?;
            let inner = concat_docs(&[r_line(), pretty_var_value2]);
            r_group(&concat_docs(&[
                pretty_func_def,
                r_text(" ="),
                r_nest(DEFAULT_TAB_SIZE, &inner),
            ]))
        } else {
            let def_line = concat_docs(&[r_text("def "), pretty_var_name.clone(), r_text(" : ")]);
            let name_str = var_name.borrow(py).pretty();
            let nest_amount = "def ".len() as i64 + name_str.chars().count() as i64 + DEFAULT_TAB_SIZE;
            r_group(&concat_docs(&[
                def_line,
                r_nest(nest_amount, &pretty_var_type),
                r_line(),
                r_text("= "),
                r_nest(DEFAULT_TAB_SIZE, &pretty_var_value),
            ]))
        };
        return Ok(r_group(&concat_docs(&[
            full_type,
            r_hard_line(),
            r_hard_line(),
            pretty_body,
        ])));
    }
    // STypeAbstraction
    if let Ok(ta) = sterm.downcast::<STypeAbstraction>() {
        let ta_b = ta.borrow();
        let name = ta_b.name.clone_ref(py);
        let kind = ta_b.kind.clone_ref(py);
        let body = ta_b.body.clone_ref(py);
        drop(ta_b);
        let pretty_name = r_text(&name.borrow(py).pretty());
        let pretty_kind = r_text(&kind.bind(py).str()?.to_string());
        let pretty_body = pretty_sterm_with_parens(
            py,
            body.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::APPLICATION, child_side: Side::RIGHT },
            depth + 1,
        )?;
        let kind_def = concat_docs(&[pretty_name, r_text(" : "), pretty_kind]);
        let binding = concat_docs(&[kind_def, r_text("."), pretty_body]);
        let _ = ctx;
        return Ok(r_group(&concat_docs(&[r_text("ƛ"), binding])));
    }
    // SRefinementAbstraction
    if let Ok(ra) = sterm.downcast::<SRefinementAbstraction>() {
        let ra_b = ra.borrow();
        let name = ra_b.name.clone_ref(py);
        let sort = ra_b.sort.clone_ref(py);
        let body = ra_b.body.clone_ref(py);
        drop(ra_b);
        let pretty_body = pretty_sterm_with_parens(
            py,
            body.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::APPLICATION, child_side: Side::RIGHT },
            depth + 1,
        )?;
        let pretty_sort = stype_pretty_internal(
            py,
            sort.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::LITERAL, child_side: Side::NONE },
        )?;
        let pretty_name = r_text(&name.borrow(py).pretty());
        let _ = ctx;
        return Ok(r_group(&concat_docs(&[
            r_text("Λ<"),
            pretty_name,
            r_text(" : "),
            pretty_sort,
            r_text(" -> Bool>=> "),
            pretty_body,
        ])));
    }
    // STypeApplication
    if let Ok(tap) = sterm.downcast::<STypeApplication>() {
        let tap_b = tap.borrow();
        let body = tap_b.body.clone_ref(py);
        drop(tap_b);
        let pretty_body = sterm_pretty_internal(
            py,
            body.bind(py),
            &ParenthesisContext { parent_precedence: Precedence::APPLICATION, child_side: Side::LEFT },
            depth + 1,
        )?;
        let _ = ctx;
        return Ok(r_group(&pretty_body));
    }
    // Fallback
    Ok(r_text(&sterm.str()?.to_string()))
}

// ---------------------------------------------------------------------------
// normalize_term / simplify_sterm
// ---------------------------------------------------------------------------

fn bool_literal_value(py: Python<'_>, sterm: &Bound<'_, PyAny>) -> Option<bool> {
    let lit = sterm.downcast::<SLiteral>().ok()?;
    let lit_b = lit.borrow();
    let type_ = lit_b.type_.bind(py);
    let tc = type_.downcast::<STypeConstructor>().ok()?;
    let tc_b = tc.borrow();
    let is_bool = {
        let n = tc_b.name.borrow(py);
        n.id == 0 && n.name == "Bool" && tc_b.args.bind(py).len() == 0
    };
    drop(tc_b);
    if !is_bool {
        return None;
    }
    let v = lit_b.value.bind(py);
    v.extract::<bool>().ok()
}

fn name_key(py: Python<'_>, n: &Py<Name>) -> (String, i64) {
    let nb = n.borrow(py);
    (nb.name.clone(), nb.id)
}

/// Recursively normalize a sugar term, performing constant-condition
/// `if` folding and beta-reducing `(\x -> body) arg`.
fn normalize_term(
    py: Python<'_>,
    term: PyObject,
    context: &mut Vec<((String, i64), PyObject)>,
    seen: &mut Vec<(String, i64)>,
) -> PyResult<PyObject> {
    let term_b = term.bind(py);
    // SLiteral: rebuild
    if let Ok(lit) = term_b.downcast::<SLiteral>() {
        let lit_b = lit.borrow();
        let value = lit_b.value.clone_ref(py);
        let type_ = lit_b.type_.clone_ref(py);
        drop(lit_b);
        let cls = py.import_bound("aeon_rs")?.getattr("SLiteral")?;
        let kw = pyo3::types::PyDict::new_bound(py);
        kw.set_item("value", value)?;
        kw.set_item("type", type_)?;
        return Ok(cls.call((), Some(&kw))?.unbind());
    }
    // SVar — resolve via context if unseen
    if let Ok(v) = term_b.downcast::<SVar>() {
        let v_b = v.borrow();
        let name = v_b.name.clone_ref(py);
        drop(v_b);
        let key = name_key(py, &name);
        if seen.iter().any(|k| *k == key) {
            // build SVar(name=name)
            let cls = py.import_bound("aeon_rs")?.getattr("SVar")?;
            return Ok(cls.call1((name,))?.unbind());
        }
        // Find context entry
        if let Some(pos) = context.iter().position(|(k, _)| *k == key) {
            let simplified = context[pos].1.clone_ref(py);
            let mut new_seen = seen.clone();
            new_seen.push(key);
            return normalize_term(py, simplified, context, &mut new_seen);
        }
        let cls = py.import_bound("aeon_rs")?.getattr("SVar")?;
        return Ok(cls.call1((name,))?.unbind());
    }
    if let Ok(h) = term_b.downcast::<SHole>() {
        let h_b = h.borrow();
        let name = h_b.name.clone_ref(py);
        drop(h_b);
        let cls = py.import_bound("aeon_rs")?.getattr("SHole")?;
        return Ok(cls.call1((name,))?.unbind());
    }
    if let Ok(by) = term_b.downcast::<SBy>() {
        let by_b = by.borrow();
        let steps = by_b.steps.clone_ref(py);
        let loc = by_b.loc.clone_ref(py);
        drop(by_b);
        let cls = py.import_bound("aeon_rs")?.getattr("SBy")?;
        let kw = pyo3::types::PyDict::new_bound(py);
        kw.set_item("steps", steps)?;
        kw.set_item("loc", loc)?;
        return Ok(cls.call((), Some(&kw))?.unbind());
    }
    if let Ok(ann) = term_b.downcast::<SAnnotation>() {
        let ann_b = ann.borrow();
        let expr = ann_b.expr.clone_ref(py);
        let type_ = ann_b.type_.clone_ref(py);
        drop(ann_b);
        let simplified_expr = normalize_term(py, expr, context, seen)?;
        let cls = py.import_bound("aeon_rs")?.getattr("SAnnotation")?;
        let kw = pyo3::types::PyDict::new_bound(py);
        kw.set_item("expr", simplified_expr)?;
        kw.set_item("type", type_)?;
        return Ok(cls.call((), Some(&kw))?.unbind());
    }
    if let Ok(iff) = term_b.downcast::<SIf>() {
        let iff_b = iff.borrow();
        let cond = iff_b.cond.clone_ref(py);
        let then = iff_b.then.clone_ref(py);
        let otherwise = iff_b.otherwise.clone_ref(py);
        drop(iff_b);
        let simplified_cond = normalize_term(py, cond, context, seen)?;
        let cond_b = simplified_cond.bind(py);
        if let Some(b) = bool_literal_value(py, cond_b) {
            if b {
                return normalize_term(py, then, context, seen);
            } else {
                return normalize_term(py, otherwise, context, seen);
            }
        }
        let s_then = normalize_term(py, then, context, seen)?;
        let s_other = normalize_term(py, otherwise, context, seen)?;
        let cls = py.import_bound("aeon_rs")?.getattr("SIf")?;
        let kw = pyo3::types::PyDict::new_bound(py);
        kw.set_item("cond", simplified_cond)?;
        kw.set_item("then", s_then)?;
        kw.set_item("otherwise", s_other)?;
        return Ok(cls.call((), Some(&kw))?.unbind());
    }
    if let Ok(app) = term_b.downcast::<SApplication>() {
        let app_b = app.borrow();
        let fun = app_b.fun.clone_ref(py);
        let arg = app_b.arg.clone_ref(py);
        drop(app_b);
        let s_fun = normalize_term(py, fun, context, seen)?;
        let s_arg = normalize_term(py, arg, context, seen)?;
        if let Ok(abs) = s_fun.bind(py).downcast::<SAbstraction>() {
            let abs_b = abs.borrow();
            let vn = abs_b.var_name.clone_ref(py);
            let body = abs_b.body.clone_ref(py);
            drop(abs_b);
            let key = name_key(py, &vn);
            // mutate context by extending — push and later pop
            context.push((key, s_arg));
            let out = normalize_term(py, body, context, seen);
            context.pop();
            return out;
        }
        let cls = py.import_bound("aeon_rs")?.getattr("SApplication")?;
        let kw = pyo3::types::PyDict::new_bound(py);
        kw.set_item("fun", s_fun)?;
        kw.set_item("arg", s_arg)?;
        return Ok(cls.call((), Some(&kw))?.unbind());
    }
    if let Ok(abs) = term_b.downcast::<SAbstraction>() {
        let abs_b = abs.borrow();
        let vn = abs_b.var_name.clone_ref(py);
        let body = abs_b.body.clone_ref(py);
        drop(abs_b);
        let s_body = normalize_term(py, body, context, seen)?;
        let cls = py.import_bound("aeon_rs")?.getattr("SAbstraction")?;
        let kw = pyo3::types::PyDict::new_bound(py);
        kw.set_item("var_name", vn)?;
        kw.set_item("body", s_body)?;
        return Ok(cls.call((), Some(&kw))?.unbind());
    }
    if let Ok(lt) = term_b.downcast::<SLet>() {
        let lt_b = lt.borrow();
        let var_name = lt_b.var_name.clone_ref(py);
        let var_value = lt_b.var_value.clone_ref(py);
        let body = lt_b.body.clone_ref(py);
        drop(lt_b);
        let body_b = body.bind(py);
        if let Ok(h) = body_b.downcast::<SHole>() {
            let h_b = h.borrow();
            let name = h_b.name.clone_ref(py);
            drop(h_b);
            let new_value = normalize_term(py, var_value, context, seen)?;
            let svar_cls = py.import_bound("aeon_rs")?.getattr("SVar")?;
            let body_var = svar_cls.call1((name.clone_ref(py),))?.unbind();
            let cls = py.import_bound("aeon_rs")?.getattr("SLet")?;
            let kw = pyo3::types::PyDict::new_bound(py);
            kw.set_item("var_name", name)?;
            kw.set_item("var_value", new_value)?;
            kw.set_item("body", body_var)?;
            return Ok(cls.call((), Some(&kw))?.unbind());
        }
        let new_value = normalize_term(py, var_value, context, seen)?;
        let new_body = normalize_term(py, body, context, seen)?;
        let cls = py.import_bound("aeon_rs")?.getattr("SLet")?;
        let kw = pyo3::types::PyDict::new_bound(py);
        kw.set_item("var_name", var_name)?;
        kw.set_item("var_value", new_value)?;
        kw.set_item("body", new_body)?;
        return Ok(cls.call((), Some(&kw))?.unbind());
    }
    if let Ok(rec) = term_b.downcast::<SRec>() {
        let rec_b = rec.borrow();
        let var_name = rec_b.var_name.clone_ref(py);
        let var_type = rec_b.var_type.clone_ref(py);
        let var_value = rec_b.var_value.clone_ref(py);
        let body = rec_b.body.clone_ref(py);
        let db = rec_b.decreasing_by.clone_ref(py);
        drop(rec_b);
        let mut new_db: Vec<PyObject> = Vec::new();
        let db_b = db.bind(py);
        for i in 0..db_b.len() {
            let item = db_b.get_item(i)?;
            new_db.push(normalize_term(py, item.unbind(), context, seen)?);
        }
        let db_tuple = PyTuple::new_bound(py, new_db.iter()).unbind();
        let body_b = body.bind(py);
        if let Ok(h) = body_b.downcast::<SHole>() {
            let h_b = h.borrow();
            let name = h_b.name.clone_ref(py);
            drop(h_b);
            let new_value = normalize_term(py, var_value, context, seen)?;
            let svar_cls = py.import_bound("aeon_rs")?.getattr("SVar")?;
            let body_var = svar_cls.call1((name.clone_ref(py),))?.unbind();
            let cls = py.import_bound("aeon_rs")?.getattr("SRec")?;
            let kw = pyo3::types::PyDict::new_bound(py);
            kw.set_item("var_name", name)?;
            kw.set_item("var_type", var_type)?;
            kw.set_item("var_value", new_value)?;
            kw.set_item("body", body_var)?;
            kw.set_item("decreasing_by", db_tuple)?;
            return Ok(cls.call((), Some(&kw))?.unbind());
        }
        let new_value = normalize_term(py, var_value, context, seen)?;
        let new_body = normalize_term(py, body, context, seen)?;
        let cls = py.import_bound("aeon_rs")?.getattr("SRec")?;
        let kw = pyo3::types::PyDict::new_bound(py);
        kw.set_item("var_name", var_name)?;
        kw.set_item("var_type", var_type)?;
        kw.set_item("var_value", new_value)?;
        kw.set_item("body", new_body)?;
        kw.set_item("decreasing_by", db_tuple)?;
        return Ok(cls.call((), Some(&kw))?.unbind());
    }
    if let Ok(ta) = term_b.downcast::<STypeAbstraction>() {
        let ta_b = ta.borrow();
        let name = ta_b.name.clone_ref(py);
        let kind = ta_b.kind.clone_ref(py);
        let body = ta_b.body.clone_ref(py);
        drop(ta_b);
        let s_body = normalize_term(py, body, context, seen)?;
        let cls = py.import_bound("aeon_rs")?.getattr("STypeAbstraction")?;
        let kw = pyo3::types::PyDict::new_bound(py);
        kw.set_item("name", name)?;
        kw.set_item("kind", kind)?;
        kw.set_item("body", s_body)?;
        return Ok(cls.call((), Some(&kw))?.unbind());
    }
    if let Ok(ra) = term_b.downcast::<SRefinementAbstraction>() {
        let ra_b = ra.borrow();
        let name = ra_b.name.clone_ref(py);
        let sort = ra_b.sort.clone_ref(py);
        let body = ra_b.body.clone_ref(py);
        drop(ra_b);
        let s_body = normalize_term(py, body, context, seen)?;
        let cls = py.import_bound("aeon_rs")?.getattr("SRefinementAbstraction")?;
        let kw = pyo3::types::PyDict::new_bound(py);
        kw.set_item("name", name)?;
        kw.set_item("sort", sort)?;
        kw.set_item("body", s_body)?;
        return Ok(cls.call((), Some(&kw))?.unbind());
    }
    // Fallback
    Ok(term)
}

fn simplify_sterm(py: Python<'_>, term: PyObject) -> PyResult<PyObject> {
    let mut context: Vec<((String, i64), PyObject)> = Vec::new();
    let mut seen: Vec<(String, i64)> = Vec::new();
    let normalized = normalize_term(py, term, &mut context, &mut seen)?;
    // rename_unused_variables is a no-op currently
    Ok(normalized)
}

// ---------------------------------------------------------------------------
// node_pretty
// ---------------------------------------------------------------------------

fn node_pretty_internal(py: Python<'_>, node: &Bound<'_, PyAny>) -> PyResult<Doc> {
    if let Ok(imp) = node.downcast::<ImportAe>() {
        let imp_b = imp.borrow();
        let module_path = imp_b.module_path.clone();
        let selected_names = imp_b.selected_names.clone_ref(py);
        let is_open = imp_b.is_open;
        drop(imp_b);
        if is_open {
            return Ok(r_group(&concat_docs(&[
                r_text("open"),
                r_line(),
                r_text(&module_path),
            ])));
        }
        let sn = selected_names.bind(py);
        if !sn.is_empty() {
            let mut parts: Vec<String> = Vec::with_capacity(sn.len());
            for i in 0..sn.len() {
                let item = sn.get_item(i)?;
                parts.push(item.str()?.to_string());
            }
            let names = parts.join(", ");
            return Ok(r_group(&concat_docs(&[
                r_text("import"),
                r_line(),
                r_text(&module_path),
                r_line(),
                r_text(&format!("({})", names)),
            ])));
        }
        return Ok(r_group(&concat_docs(&[
            r_text("import"),
            r_line(),
            r_text(&module_path),
        ])));
    }
    if let Ok(td) = node.downcast::<TypeDecl>() {
        let td_b = td.borrow();
        let n = td_b.name.borrow(py).pretty();
        return Ok(r_group(&concat_docs(&[
            r_text("type"),
            r_line(),
            r_text(&n),
        ])));
    }
    if let Ok(dec) = node.downcast::<Decorator>() {
        let dec_b = dec.borrow();
        let name = dec_b.name.clone_ref(py);
        let macro_args = dec_b.macro_args.clone_ref(py);
        drop(dec_b);
        let ma_b = macro_args.bind(py);
        let mut pretty_args: Vec<Doc> = Vec::with_capacity(ma_b.len());
        for i in 0..ma_b.len() {
            let arg = ma_b.get_item(i)?;
            let simplified = simplify_sterm(py, arg.unbind())?;
            let d = sterm_pretty_internal(
                py,
                simplified.bind(py),
                &ParenthesisContext {
                    parent_precedence: Precedence::LITERAL,
                    child_side: Side::NONE,
                },
                0,
            )?;
            pretty_args.push(d);
        }
        let sep = concat_docs(&[r_text(","), r_line()]);
        let args_doc = r_insert_between(&sep, &pretty_args);
        let parens_doc = r_parens(&args_doc, false);
        return Ok(concat_docs(&[
            r_text("@"),
            r_text(&name.borrow(py).pretty()),
            parens_doc,
        ]));
    }
    if let Ok(ind) = node.downcast::<InductiveDecl>() {
        let ind_b = ind.borrow();
        let name = ind_b.name.clone_ref(py);
        let args = ind_b.args.clone_ref(py);
        let rforalls = ind_b.rforalls.clone_ref(py);
        let constructors = ind_b.constructors.clone_ref(py);
        let measures = ind_b.measures.clone_ref(py);
        drop(ind_b);

        let pretty_name = concat_docs(&[
            r_text("inductive"),
            r_line(),
            r_text(&name.borrow(py).pretty()),
        ]);

        // pretty_args: group(insert_between(line(), [text(arg.pretty()) for arg in args]))
        let args_b = args.bind(py);
        let mut args_docs: Vec<Doc> = Vec::with_capacity(args_b.len());
        for i in 0..args_b.len() {
            let arg = args_b.get_item(i)?;
            // arg has a .pretty() method (Name)
            let pretty = arg.call_method0("pretty")?.extract::<String>()?;
            args_docs.push(r_text(&pretty));
        }
        let pretty_args = r_group(&r_insert_between(&r_line(), &args_docs));

        let rforalls_b = rforalls.bind(py);
        let mut rforalls_docs: Vec<Doc> = Vec::with_capacity(rforalls_b.len());
        for i in 0..rforalls_b.len() {
            let tup = rforalls_b.get_item(i)?;
            let rho = tup.get_item(0)?;
            let sort = tup.get_item(1)?;
            let rho_str = rho.call_method0("pretty")?.extract::<String>()?;
            let sort_doc = stype_pretty_internal(
                py,
                &sort,
                &ParenthesisContext {
                    parent_precedence: Precedence::LITERAL,
                    child_side: Side::NONE,
                },
            )?;
            rforalls_docs.push(concat_docs(&[
                r_text("forall"),
                r_text(" <"),
                r_text(&rho_str),
                r_text(" : "),
                sort_doc,
                r_text(" -> Bool>"),
            ]));
        }
        let pretty_rforalls = r_group(&r_insert_between(&r_line(), &rforalls_docs));

        let cons_b = constructors.bind(py);
        let mut cons_docs: Vec<Doc> = Vec::with_capacity(cons_b.len());
        for i in 0..cons_b.len() {
            let item = cons_b.get_item(i)?;
            let d = node_pretty_internal(py, &item)?;
            cons_docs.push(concat_docs(&[r_text("| "), d]));
        }
        let pretty_constructors = r_group(&r_insert_between(&r_line(), &cons_docs));

        let meas_b = measures.bind(py);
        let mut meas_docs: Vec<Doc> = Vec::with_capacity(meas_b.len());
        for i in 0..meas_b.len() {
            let item = meas_b.get_item(i)?;
            let d = node_pretty_internal(py, &item)?;
            meas_docs.push(concat_docs(&[r_text("+ "), d]));
        }
        let pretty_measures = r_group(&r_insert_between(&r_line(), &meas_docs));

        let mut chunks: Vec<Doc> = vec![pretty_name, pretty_args];
        if rforalls_b.len() > 0 {
            chunks.push(pretty_rforalls);
        }
        chunks.push(pretty_constructors);
        chunks.push(pretty_measures);
        return Ok(r_group(&r_insert_between(&r_line(), &chunks)));
    }
    if let Ok(defn) = node.downcast::<Definition>() {
        let defn_b = defn.borrow();
        let name = defn_b.name.clone_ref(py);
        let foralls = defn_b.foralls.clone_ref(py);
        let args = defn_b.args.clone_ref(py);
        let type_ = defn_b.type_.clone_ref(py);
        let body0 = defn_b.body.clone_ref(py);
        let decorators = defn_b.decorators.clone_ref(py);
        let rforalls = defn_b.rforalls.clone_ref(py);
        drop(defn_b);

        // Build current body / type by wrapping with abstractions / abstraction
        // types matching the Python code.
        let args_b = args.bind(py);
        let n_args = args_b.len();
        let rforalls_b = rforalls.bind(py);
        let n_rforalls = rforalls_b.len();
        let foralls_b = foralls.bind(py);
        let n_foralls = foralls_b.len();

        // Wrap body with SAbstraction (reversed args)
        let mut body = body0;
        for i in (0..n_args).rev() {
            let tup = args_b.get_item(i)?;
            let vn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let abs_cls = py.import_bound("aeon_rs")?.getattr("SAbstraction")?;
            let kw = pyo3::types::PyDict::new_bound(py);
            kw.set_item("var_name", vn)?;
            kw.set_item("body", body)?;
            body = abs_cls.call((), Some(&kw))?.unbind();
        }
        // Wrap type with SAbstractionType (reversed args)
        let mut type_obj = type_;
        for i in (0..n_args).rev() {
            let tup = args_b.get_item(i)?;
            let vn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let vt: PyObject = tup.get_item(1)?.unbind();
            let cls = py.import_bound("aeon_rs")?.getattr("SAbstractionType")?;
            let kw = pyo3::types::PyDict::new_bound(py);
            kw.set_item("var_name", vn)?;
            kw.set_item("var_type", vt)?;
            kw.set_item("type", type_obj)?;
            type_obj = cls.call((), Some(&kw))?.unbind();
        }
        // Wrap with SRefinementPolymorphism / SRefinementAbstraction (reversed)
        for i in (0..n_rforalls).rev() {
            let tup = rforalls_b.get_item(i)?;
            let rn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let rs: PyObject = tup.get_item(1)?.unbind();
            let cls_type = py.import_bound("aeon_rs")?.getattr("SRefinementPolymorphism")?;
            let kw1 = pyo3::types::PyDict::new_bound(py);
            kw1.set_item("name", rn.clone_ref(py))?;
            kw1.set_item("sort", rs.clone_ref(py))?;
            kw1.set_item("body", type_obj)?;
            type_obj = cls_type.call((), Some(&kw1))?.unbind();
            let cls_body = py.import_bound("aeon_rs")?.getattr("SRefinementAbstraction")?;
            let kw2 = pyo3::types::PyDict::new_bound(py);
            kw2.set_item("name", rn)?;
            kw2.set_item("sort", rs)?;
            kw2.set_item("body", body)?;
            body = cls_body.call((), Some(&kw2))?.unbind();
        }
        // Wrap body with STypeAbstraction (reversed foralls)
        for i in (0..n_foralls).rev() {
            let tup = foralls_b.get_item(i)?;
            let tn: Py<Name> = tup.get_item(0)?.downcast::<Name>()?.clone().unbind();
            let k: PyObject = tup.get_item(1)?.unbind();
            let cls = py.import_bound("aeon_rs")?.getattr("STypeAbstraction")?;
            let kw = pyo3::types::PyDict::new_bound(py);
            kw.set_item("name", tn)?;
            kw.set_item("kind", k)?;
            kw.set_item("body", body)?;
            body = cls.call((), Some(&kw))?.unbind();
        }

        // Decorators
        let decs_b = decorators.bind(py);
        let mut dec_docs: Vec<Doc> = Vec::with_capacity(decs_b.len());
        for i in 0..decs_b.len() {
            let item = decs_b.get_item(i)?;
            let d = node_pretty_internal(py, &item)?;
            dec_docs.push(d);
        }
        let pretty_decorators = r_insert_between(&r_line(), &dec_docs);

        let definition_doc = if type_obj.bind(py).downcast::<SAbstractionType>().is_ok() {
            let (named_vars, final_type) = unwrap_abstraction_types(py, type_obj)?;
            let name_doc = r_text(&name.borrow(py).pretty());
            let (pretty_func_def, _alignment) =
                pretty_print_function_definition(py, &name_doc, &named_vars, final_type.bind(py))?;
            let stripped = strip_matching_abstractions(py, body, &named_vars)?;
            let pretty_body = pretty_sterm_with_parens(
                py,
                stripped.bind(py),
                &ParenthesisContext { parent_precedence: Precedence::LET, child_side: Side::NONE },
                1,
            )?;
            let inner = concat_docs(&[r_line(), pretty_body]);
            r_group(&concat_docs(&[
                pretty_func_def,
                r_text(" ="),
                r_nest(DEFAULT_TAB_SIZE, &inner),
            ]))
        } else {
            let pretty_var_name = name.borrow(py).pretty();
            let pretty_var_type = stype_pretty_internal(
                py,
                type_obj.bind(py),
                &ParenthesisContext {
                    parent_precedence: Precedence::LITERAL,
                    child_side: Side::NONE,
                },
            )?;
            let pretty_body = sterm_pretty_internal(
                py,
                body.bind(py),
                &ParenthesisContext {
                    parent_precedence: Precedence::LITERAL,
                    child_side: Side::NONE,
                },
                1,
            )?;
            let def_line = concat_docs(&[
                r_text("def "),
                r_text(&pretty_var_name),
                r_text(" : "),
            ]);
            let nest_amt =
                ("def ".len() as i64) + (pretty_var_name.chars().count() as i64) + DEFAULT_TAB_SIZE;
            r_group(&concat_docs(&[
                def_line,
                r_nest(nest_amt, &pretty_var_type),
                r_line(),
                r_text("= "),
                r_nest(DEFAULT_TAB_SIZE, &pretty_body),
            ]))
        };

        let dec_break = if decs_b.len() > 0 { r_hard_line() } else { r_nil() };
        return Ok(r_group(&concat_docs(&[
            pretty_decorators,
            dec_break,
            definition_doc,
        ])));
    }
    if let Ok(prog) = node.downcast::<Program>() {
        let prog_b = prog.borrow();
        let imports = prog_b.imports.clone_ref(py);
        let type_decls = prog_b.type_decls.clone_ref(py);
        let inductive_decls = prog_b.inductive_decls.clone_ref(py);
        let definitions = prog_b.definitions.clone_ref(py);
        drop(prog_b);

        fn block(
            py: Python<'_>,
            lst: &Py<PyList>,
            sep: Doc,
        ) -> PyResult<Doc> {
            let lb = lst.bind(py);
            if lb.is_empty() {
                return Ok(r_nil());
            }
            let mut docs: Vec<Doc> = Vec::with_capacity(lb.len());
            for i in 0..lb.len() {
                let item = lb.get_item(i)?;
                docs.push(node_pretty_internal(py, &item)?);
            }
            Ok(r_group(&r_insert_between(&sep, &docs)))
        }

        let imports_doc = block(py, &imports, r_line())?;
        let type_decls_doc = block(py, &type_decls, r_line())?;
        let ind_doc = block(py, &inductive_decls, r_line())?;
        let defs_doc = block(py, &definitions, concat_docs(&[r_hard_line(), r_hard_line()]))?;

        let blocks = [imports_doc, type_decls_doc, ind_doc, defs_doc];
        let non_nil: Vec<Doc> = blocks
            .into_iter()
            .filter(|b| !b.node.is_nil())
            .collect();
        let sep = concat_docs(&[r_hard_line(), r_hard_line()]);
        return Ok(r_group(&r_insert_between(&sep, &non_nil)));
    }
    Ok(r_nil())
}

// ---------------------------------------------------------------------------
// Public API (exposed to Python)
// ---------------------------------------------------------------------------

#[pyfunction]
#[pyo3(signature = (stype, context = None))]
pub fn stype_pretty(
    py: Python<'_>,
    stype: PyObject,
    context: Option<PyObject>,
) -> PyResult<Doc> {
    let ctx = match context {
        None => ParenthesisContext {
            parent_precedence: Precedence::LITERAL,
            child_side: Side::NONE,
        },
        Some(obj) => {
            let b = obj.bind(py);
            let pc = b.downcast::<ParenthesisContext>().map_err(|_| {
                PyValueError::new_err("stype_pretty: context must be ParenthesisContext")
            })?;
            pc.borrow().clone()
        }
    };
    stype_pretty_internal(py, stype.bind(py), &ctx)
}

#[pyfunction]
#[pyo3(signature = (sterm, context = None, depth = 0))]
pub fn sterm_pretty(
    py: Python<'_>,
    sterm: PyObject,
    context: Option<PyObject>,
    depth: i64,
) -> PyResult<Doc> {
    let ctx = match context {
        None => ParenthesisContext {
            parent_precedence: Precedence::LITERAL,
            child_side: Side::NONE,
        },
        Some(obj) => {
            let b = obj.bind(py);
            let pc = b.downcast::<ParenthesisContext>().map_err(|_| {
                PyValueError::new_err("sterm_pretty: context must be ParenthesisContext")
            })?;
            pc.borrow().clone()
        }
    };
    sterm_pretty_internal(py, sterm.bind(py), &ctx, depth)
}

#[pyfunction]
pub fn pretty_print_sterm(py: Python<'_>, term: PyObject) -> PyResult<String> {
    let simplified = simplify_sterm(py, term)?;
    let doc = sterm_pretty_internal(
        py,
        simplified.bind(py),
        &ParenthesisContext {
            parent_precedence: Precedence::LITERAL,
            child_side: Side::NONE,
        },
        0,
    )?;
    Ok(doc.__str__())
}

#[pyfunction]
pub fn pretty_print_node(py: Python<'_>, node: PyObject) -> PyResult<String> {
    let doc = node_pretty_internal(py, node.bind(py))?;
    Ok(doc.__str__())
}

#[pyfunction]
pub fn node_pretty(py: Python<'_>, node: PyObject) -> PyResult<Doc> {
    node_pretty_internal(py, node.bind(py))
}

#[pyfunction]
#[pyo3(signature = (term, context = None))]
pub fn normalize_term_py(
    py: Python<'_>,
    term: PyObject,
    context: Option<PyObject>,
) -> PyResult<PyObject> {
    // Accept optional `context` dict for parity with Python; ignored beyond
    // initial seeding (caller-only usage).
    let mut ctx: Vec<((String, i64), PyObject)> = Vec::new();
    if let Some(c) = context {
        let d = c.bind(py).downcast::<pyo3::types::PyDict>().ok();
        if let Some(dd) = d {
            for (k, v) in dd.iter() {
                if let Ok(n) = k.downcast::<Name>() {
                    let nb = n.borrow();
                    ctx.push(((nb.name.clone(), nb.id), v.unbind()));
                }
            }
        }
    }
    let mut seen: Vec<(String, i64)> = Vec::new();
    normalize_term(py, term, &mut ctx, &mut seen)
}

#[pyfunction]
pub fn simplify_sterm_py(py: Python<'_>, term: PyObject) -> PyResult<PyObject> {
    simplify_sterm(py, term)
}

#[pyfunction]
pub fn needs_parens_aux(
    child_associativity: Associativity,
    child_precedence: Precedence,
    child_side: Side,
    parent_precedence: Precedence,
) -> bool {
    needs_parens_aux_internal(child_associativity, child_precedence, child_side, parent_precedence)
}

#[pyfunction]
pub fn needs_parens(child_operation: Operation, ctx: &ParenthesisContext) -> bool {
    needs_parens_internal(child_operation, ctx)
}
