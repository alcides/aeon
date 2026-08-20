//! Pure-string superscript / subscript translation tables.
//! Port of `aeon.utils.superscripts`.

use pyo3::prelude::*;

/// (ascii char, mapped superscript char). The table is small; a linear
/// scan inside `translate_one` is fast enough.
const SUPERSCRIPT: &[(char, &str)] = &[
    ('0', "⁰"), ('1', "¹"), ('2', "²"), ('3', "³"), ('4', "⁴"),
    ('5', "⁵"), ('6', "⁶"), ('7', "⁷"), ('8', "⁸"), ('9', "⁹"),
    ('a', "ᵃ"), ('b', "ᵇ"), ('c', "ᶜ"), ('d', "ᵈ"), ('e', "ᵉ"),
    ('f', "ᶠ"), ('g', "ᵍ"), ('h', "ʰ"), ('i', "ᶦ"), ('j', "ʲ"),
    ('k', "ᵏ"), ('l', "ˡ"), ('m', "ᵐ"), ('n', "ⁿ"), ('o', "ᵒ"),
    ('p', "ᵖ"), ('q', "۹"), ('r', "ʳ"), ('s', "ˢ"), ('t', "ᵗ"),
    ('u', "ᵘ"), ('v', "ᵛ"), ('w', "ʷ"), ('x', "ˣ"), ('y', "ʸ"),
    ('z', "ᶻ"),
    ('A', "ᴬ"), ('B', "ᴮ"), ('C', "ᶜ"), ('D', "ᴰ"), ('E', "ᴱ"),
    ('F', "ᶠ"), ('G', "ᴳ"), ('H', "ᴴ"), ('I', "ᴵ"), ('J', "ᴶ"),
    ('K', "ᴷ"), ('L', "ᴸ"), ('M', "ᴹ"), ('N', "ᴺ"), ('O', "ᴼ"),
    ('P', "ᴾ"), ('Q', "Q"), ('R', "ᴿ"), ('S', "ˢ"), ('T', "ᵀ"),
    ('U', "ᵁ"), ('V', "ⱽ"), ('W', "ᵂ"), ('X', "ˣ"), ('Y', "ʸ"),
    ('Z', "ᶻ"),
    ('+', "⁺"), ('-', "⁻"), ('=', "⁼"), ('(', "⁽"), (')', "⁾"),
];

const SUBSCRIPT: &[(char, &str)] = &[
    ('0', "₀"), ('1', "₁"), ('2', "₂"), ('3', "₃"), ('4', "₄"),
    ('5', "₅"), ('6', "₆"), ('7', "₇"), ('8', "₈"), ('9', "₉"),
    ('a', "ₐ"), ('b', "♭"), ('c', "꜀"), ('d', "ᑯ"), ('e', "ₑ"),
    ('f', "բ"), ('g', "₉"), ('h', "ₕ"), ('i', "ᵢ"), ('j', "ⱼ"),
    ('k', "ₖ"), ('l', "ₗ"), ('m', "ₘ"), ('n', "ₙ"), ('o', "ₒ"),
    ('p', "ₚ"), ('q', "૧"), ('r', "ᵣ"), ('s', "ₛ"), ('t', "ₜ"),
    ('u', "ᵤ"), ('v', "ᵥ"), ('w', "w"), ('x', "ₓ"), ('y', "ᵧ"),
    ('z', "₂"),
    ('A', "ₐ"), ('B', "₈"), ('C', "C"), ('D', "D"), ('E', "ₑ"),
    ('F', "բ"), ('G', "G"), ('H', "ₕ"), ('I', "ᵢ"), ('J', "ⱼ"),
    ('K', "ₖ"), ('L', "ₗ"), ('M', "ₘ"), ('N', "ₙ"), ('O', "ₒ"),
    ('P', "ₚ"), ('Q', "Q"), ('R', "ᵣ"), ('S', "ₛ"), ('T', "ₜ"),
    ('U', "ᵤ"), ('V', "ᵥ"), ('W', "w"), ('X', "ₓ"), ('Y', "ᵧ"),
    ('Z', "Z"),
    ('+', "₊"), ('-', "₋"), ('=', "₌"), ('(', "₍"), (')', "₎"),
];

fn translate(s: &str, table: &[(char, &str)]) -> String {
    let mut out = String::with_capacity(s.len() * 2);
    for c in s.chars() {
        let mut replaced = false;
        for (k, v) in table {
            if *k == c {
                out.push_str(v);
                replaced = true;
                break;
            }
        }
        if !replaced {
            out.push(c);
        }
    }
    out
}

#[pyfunction]
pub fn superscript(s: &str) -> String {
    translate(s, SUPERSCRIPT)
}

#[pyfunction]
pub fn subscript(s: &str) -> String {
    translate(s, SUBSCRIPT)
}
