from typing import Any, Callable
from aeon.core.terms import Term
from aeon.sugar.program import Definition

Metadata = dict[str, Any]
DecoratorType = Callable[[list[Term], Definition, Metadata],
                         tuple[Definition, list[Definition], Metadata]]
