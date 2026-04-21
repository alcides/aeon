from typing import Any, Callable, TYPE_CHECKING

from aeon.utils.name import Name
from aeon.sugar.program import Definition, Decorator

if TYPE_CHECKING:
    from aeon.core.terms import Term
    from aeon.typechecking.context import TypingContext

Metadata = dict[Name, Any]
DecoratorType = Callable[[Decorator, Definition, Metadata], tuple[Definition, list[Definition], Metadata]]

# Reserved metadata key for pending core-phase decorators (see ``collect_core_decorator_queue``).
CORE_DECORATOR_QUEUE_META_KEY = Name("_aeon_core_decorator_queue", -1)

CoreDecoratorType = Callable[[Decorator, Name, "TypingContext", "Term", Metadata], Metadata]


def metadata_update(metadata: Metadata, fun: Definition, aux_dict: dict[str, Any] = None) -> Metadata:
    if not aux_dict:
        aux_dict = {}
    if fun.name in metadata.keys():
        metadata[fun.name].update(aux_dict)
    else:
        metadata[fun.name] = aux_dict
    return metadata


def metadata_update_by_name(metadata: Metadata, fname: Name, aux_dict: dict[str, Any] | None = None) -> Metadata:
    """Like ``metadata_update`` but keyed by function name (no ``Definition`` object)."""
    if aux_dict is None:
        aux_dict = {}
    if fname in metadata:
        metadata[fname].update(aux_dict)
    else:
        metadata[fname] = aux_dict
    return metadata
