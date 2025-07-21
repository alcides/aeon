from dataclasses import dataclass, field

from aeon.core.liquid import LiquidLiteralBool, LiquidTerm
from aeon.core.types import AbstractionType, TypeConstructor


class SMTSolvingException(Exception):
    pass


@dataclass
class SMTQuery:
    types: list[str] = field(default_factory=list)
    functions: dict[str, AbstractionType] = field(default_factory=lambda: {})
    variables: dict[str, TypeConstructor] = field(default_factory=lambda: {})
    premises: list[LiquidTerm] = field(default_factory=list)
    conclusion: LiquidTerm = field(default_factory=lambda: LiquidLiteralBool(True))
