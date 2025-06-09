from typing import Any, Callable

from aeon.utils.name import Name
from aeon.sugar.program import Definition, STerm

Metadata = dict[Name, Any]
DecoratorType = Callable[[list[STerm], Definition, Metadata], tuple[Definition, list[Definition], Metadata]]


def metadata_update(metadata: Metadata, fun: Definition, aux_dict: dict[str, Any] = None) -> Metadata:
    if not aux_dict:
        aux_dict = {}
    if fun.name in metadata.keys():
        metadata[fun.name].update(aux_dict)
    else:
        metadata[fun.name] = aux_dict
    return metadata
