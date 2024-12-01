from typing import Any, Callable

from aeon.core.terms import Term
from aeon.sugar.program import Definition

Metadata = dict[str, Any]
DecoratorType = Callable[[list[Term], Definition, Metadata], tuple[Definition, list[Definition], Metadata]]


def metadata_update(metadata: Metadata, fun: Definition, aux_dict: dict[str, Any] = None) -> Metadata:
    if not aux_dict:
        aux_dict = {}
    if fun.name in metadata.keys():
        metadata[(str(fun.name))].update(aux_dict)
    else:
        metadata[(str(fun.name))] = aux_dict
    return metadata
