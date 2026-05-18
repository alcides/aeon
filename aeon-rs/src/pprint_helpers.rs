//! Wadler-Leijen pretty-printer `Doc` combinator library.
//! Port of `aeon.utils.pprint_helpers`.

use pyo3::exceptions::PyTypeError;
use pyo3::prelude::*;
use pyo3::types::PyList;
use std::sync::Arc;

pub const DEFAULT_NEW_LINE_CHAR: char = '\n';
pub const DEFAULT_SPACE_CHAR: char = ' ';
pub const DEFAULT_WIDTH: i64 = 120;
pub const DEFAULT_TAB_SIZE: i64 = 4;

/// Internal node — a Wadler-Leijen `Doc`. Lives behind `Arc` so cheap
/// shared structure works (mirrors the Python frozen dataclasses).
pub enum DocNode {
    Nil,
    Text(String),
    Line,
    SoftLine,
    HardLine,
    Concat(Arc<DocNode>, Arc<DocNode>),
    Nest(i64, Arc<DocNode>),
    /// Lazy group: list of alternatives produced by `alternatives()`.
    /// Always realised as `[flattened, original]`.
    Group(Arc<DocNode>),
}

impl DocNode {
    fn layout(&self, indent: i64) -> String {
        match self {
            DocNode::Nil => String::new(),
            DocNode::Text(s) => s.clone(),
            DocNode::Line | DocNode::SoftLine => {
                let mut s = String::with_capacity(1 + indent as usize);
                s.push(DEFAULT_NEW_LINE_CHAR);
                for _ in 0..indent.max(0) {
                    s.push(DEFAULT_SPACE_CHAR);
                }
                s
            }
            DocNode::HardLine => {
                let mut s = String::with_capacity(1 + indent as usize);
                s.push(DEFAULT_NEW_LINE_CHAR);
                for _ in 0..indent.max(0) {
                    s.push(DEFAULT_SPACE_CHAR);
                }
                s
            }
            DocNode::Concat(l, r) => {
                let mut s = l.layout(indent);
                s.push_str(&r.layout(indent));
                s
            }
            DocNode::Nest(n, d) => d.layout(indent + n),
            DocNode::Group(d) => {
                // Best at default width then layout.
                let chosen = d.best_group(DEFAULT_WIDTH, 0);
                chosen.layout(indent)
            }
        }
    }

    fn fits(&self, width: i64, current_length: i64) -> bool {
        match self {
            DocNode::Nil => true,
            DocNode::Text(s) => current_length + s.chars().count() as i64 <= width,
            DocNode::Line => current_length + 1 <= width,
            DocNode::SoftLine => current_length <= width,
            DocNode::HardLine => false,
            DocNode::Concat(l, r) => {
                if !l.fits(width, current_length) {
                    return false;
                }
                let nl = l.calc_new_length(current_length);
                r.fits(width, nl)
            }
            DocNode::Nest(_, d) => d.fits(width, current_length),
            DocNode::Group(d) => {
                let flat = d.flatten();
                if flat.fits(width, current_length) {
                    return true;
                }
                d.fits(width, current_length)
            }
        }
    }

    /// Drive a group: try flattened first, fall back to original.
    fn best_group(&self, width: i64, current_length: i64) -> Arc<DocNode> {
        let flat = Arc::new(self.flatten());
        if flat.fits(width, current_length) {
            return Arc::new(flat.best(width, current_length));
        }
        Arc::new(self.best(width, current_length))
    }

    fn best(&self, width: i64, current_length: i64) -> DocNode {
        match self {
            DocNode::Nil => DocNode::Nil,
            DocNode::Text(s) => DocNode::Text(s.clone()),
            DocNode::Line => DocNode::Line,
            DocNode::SoftLine => DocNode::SoftLine,
            DocNode::HardLine => DocNode::HardLine,
            DocNode::Concat(l, r) => {
                let lb = l.best(width, current_length);
                let nl = lb.calc_new_length(current_length);
                let rb = r.best(width, nl);
                DocNode::Concat(Arc::new(lb), Arc::new(rb))
            }
            DocNode::Nest(n, d) => {
                let inner = d.best(width, current_length + n);
                DocNode::Nest(*n, Arc::new(inner))
            }
            DocNode::Group(d) => {
                let flat = Arc::new(d.flatten());
                if flat.fits(width, current_length) {
                    flat.best(width, current_length)
                } else {
                    d.best(width, current_length)
                }
            }
        }
    }

    fn flatten(&self) -> DocNode {
        match self {
            DocNode::Nil => DocNode::Nil,
            DocNode::Text(s) => DocNode::Text(s.clone()),
            DocNode::Line => DocNode::Text(String::from(" ")),
            DocNode::SoftLine => DocNode::Text(String::new()),
            DocNode::HardLine => DocNode::HardLine,
            DocNode::Concat(l, r) => {
                DocNode::Concat(Arc::new(l.flatten()), Arc::new(r.flatten()))
            }
            DocNode::Nest(n, d) => DocNode::Nest(*n, Arc::new(d.flatten())),
            DocNode::Group(d) => d.flatten(),
        }
    }

    fn calc_new_length(&self, current_length: i64) -> i64 {
        match self {
            DocNode::Line | DocNode::HardLine | DocNode::SoftLine => 0,
            DocNode::Text(s) => current_length + s.chars().count() as i64,
            _ => {
                let l = self.layout(0);
                if let Some(idx) = l.rfind(DEFAULT_NEW_LINE_CHAR) {
                    let after = &l[idx + DEFAULT_NEW_LINE_CHAR.len_utf8()..];
                    after.chars().count() as i64
                } else {
                    current_length + l.chars().count() as i64
                }
            }
        }
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, DocNode::Nil)
    }
}

/// Python-visible Doc — a thin wrapper around an `Arc<DocNode>`.
#[pyclass(module = "aeon_rs")]
#[derive(Clone)]
pub struct Doc {
    pub node: Arc<DocNode>,
}

impl Doc {
    pub fn from_node(node: DocNode) -> Self {
        Doc { node: Arc::new(node) }
    }

    pub fn arc(node: Arc<DocNode>) -> Self {
        Doc { node }
    }
}

#[pymethods]
impl Doc {
    pub fn layout(&self, indent: i64) -> String {
        self.node.layout(indent)
    }

    pub fn fits(&self, width: i64, current_length: i64) -> bool {
        self.node.fits(width, current_length)
    }

    pub fn best(&self, width: i64, current_length: i64) -> Doc {
        Doc::from_node(self.node.best(width, current_length))
    }

    pub fn flatten(&self) -> Doc {
        Doc::from_node(self.node.flatten())
    }

    pub fn calculate_new_length(&self, current_length: i64) -> i64 {
        self.node.calc_new_length(current_length)
    }

    pub fn __str__(&self) -> String {
        let best = self.node.best(DEFAULT_WIDTH, 0);
        best.layout(0)
    }

    pub fn __repr__(&self) -> String {
        self.__str__()
    }

    fn __add__(&self, other: &Doc) -> Doc {
        Doc::from_node(DocNode::Concat(self.node.clone(), other.node.clone()))
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // Structural equality used only for `doc != nil()` filters in callers.
        // We approximate via rendered string + flatness.
        match other.downcast::<Doc>() {
            Ok(o) => {
                let a = self.__str__();
                let b = o.borrow().__str__();
                a == b
            }
            Err(_) => false,
        }
    }
}

// ---- Functional API -----------------------------------------------------

#[pyfunction]
pub fn nil() -> Doc {
    Doc::from_node(DocNode::Nil)
}

#[pyfunction]
pub fn text(value: &str) -> Doc {
    if value.is_empty() {
        nil()
    } else {
        Doc::from_node(DocNode::Text(value.to_string()))
    }
}

#[pyfunction]
pub fn line() -> Doc {
    Doc::from_node(DocNode::Line)
}

#[pyfunction]
pub fn soft_line() -> Doc {
    Doc::from_node(DocNode::SoftLine)
}

#[pyfunction]
pub fn hard_line() -> Doc {
    Doc::from_node(DocNode::HardLine)
}

#[pyfunction]
pub fn nest(indent: i64, doc: &Doc) -> Doc {
    Doc::from_node(DocNode::Nest(indent, doc.node.clone()))
}

#[pyfunction]
pub fn group(doc: &Doc) -> Doc {
    Doc::from_node(DocNode::Group(doc.node.clone()))
}

#[pyfunction]
#[pyo3(signature = (doc, needs_spaces = false))]
pub fn parens(py: Python<'_>, doc: &Doc, needs_spaces: bool) -> PyResult<Doc> {
    let lf: Doc = if needs_spaces { line() } else { soft_line() };
    // text("(") + nest(TAB, lf + doc) + lf + text(")")
    let open = text("(");
    let close = text(")");
    let nested_inner = concat_docs(&[lf.clone(), doc.clone()]);
    let nested = nest(DEFAULT_TAB_SIZE, &nested_inner);
    let inner = concat_docs(&[open, nested, lf, close]);
    let _ = py;
    Ok(group(&inner))
}

#[pyfunction]
pub fn concat(py: Python<'_>, docs: Bound<'_, PyList>) -> PyResult<Doc> {
    let mut filtered: Vec<Doc> = Vec::with_capacity(docs.len());
    for i in 0..docs.len() {
        let item = docs.get_item(i)?;
        let d = item
            .downcast::<Doc>()
            .map_err(|_| PyTypeError::new_err("concat expects a list of Doc"))?;
        let inner = d.borrow();
        if !inner.node.is_nil() {
            filtered.push(inner.clone());
        }
    }
    let _ = py;
    Ok(concat_docs(&filtered))
}

#[pyfunction]
pub fn insert_between(py: Python<'_>, separator: &Doc, docs: Bound<'_, PyList>) -> PyResult<Doc> {
    if docs.is_empty() {
        return Ok(nil());
    }
    let mut all: Vec<Doc> = Vec::with_capacity(docs.len());
    for i in 0..docs.len() {
        let item = docs.get_item(i)?;
        let d = item
            .downcast::<Doc>()
            .map_err(|_| PyTypeError::new_err("insert_between expects a list of Doc"))?;
        all.push(d.borrow().clone());
    }
    let _ = py;
    if all.is_empty() {
        return Ok(nil());
    }
    let mut iter = all.into_iter();
    let mut acc = iter.next().unwrap();
    for d in iter {
        acc = concat_docs(&[acc, separator.clone(), d]);
    }
    Ok(acc)
}

// ---- Rust-side helpers --------------------------------------------------

pub fn concat_docs(docs: &[Doc]) -> Doc {
    let filtered: Vec<&Doc> = docs.iter().filter(|d| !d.node.is_nil()).collect();
    if filtered.is_empty() {
        return Doc::from_node(DocNode::Nil);
    }
    let mut iter = filtered.iter();
    let mut acc = (*iter.next().unwrap()).clone();
    for d in iter {
        acc = Doc::from_node(DocNode::Concat(acc.node.clone(), d.node.clone()));
    }
    acc
}

pub fn r_text(s: &str) -> Doc {
    text(s)
}

pub fn r_nil() -> Doc {
    nil()
}

pub fn r_line() -> Doc {
    line()
}

pub fn r_soft_line() -> Doc {
    soft_line()
}

pub fn r_hard_line() -> Doc {
    hard_line()
}

pub fn r_nest(indent: i64, doc: &Doc) -> Doc {
    nest(indent, doc)
}

pub fn r_group(doc: &Doc) -> Doc {
    group(doc)
}

pub fn r_parens(doc: &Doc, needs_spaces: bool) -> Doc {
    let lf: Doc = if needs_spaces { line() } else { soft_line() };
    let open = text("(");
    let close = text(")");
    let nested_inner = concat_docs(&[lf.clone(), doc.clone()]);
    let nested = nest(DEFAULT_TAB_SIZE, &nested_inner);
    let inner = concat_docs(&[open, nested, lf, close]);
    group(&inner)
}

pub fn r_insert_between(separator: &Doc, docs: &[Doc]) -> Doc {
    if docs.is_empty() {
        return nil();
    }
    let mut iter = docs.iter();
    let mut acc = iter.next().unwrap().clone();
    for d in iter {
        acc = concat_docs(&[acc, separator.clone(), d.clone()]);
    }
    acc
}
