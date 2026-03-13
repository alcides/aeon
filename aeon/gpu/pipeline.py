from __future__ import annotations

from aeon.core.terms import Term, Rec, Abstraction, TypeAbstraction, Annotation
from aeon.gpu.gpu_validator import validate_gpu_subset
from aeon.gpu.gpu_converter import convert_to_gpu_ast, GType, GInt
from aeon.frontend.anf_converter import ensure_anf
from aeon.utils.name import Name

def compile_to_gpu(aeon_term: Term, func_name: Name, arg_names: list[Name], arg_types: list[GType] = None) -> str:
    aeon_term = ensure_anf(aeon_term)

    validate_gpu_subset(aeon_term, rec_scope={func_name})
    if arg_types is None:
        arg_types = [GInt for _ in arg_names]

    type_env = {name: ty for name, ty in zip(arg_names, arg_types)}
    gpu_ast = convert_to_gpu_ast(aeon_term, type_env=type_env)

    return "TODO"
