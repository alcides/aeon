from abc import ABC
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

from aeon.core.types import Kind
from aeon.sugar.program import STerm
from aeon.sugar.stypes import SType


class AeonError(ABC, BaseException):
    pass


@dataclass
class ImportError(AeonError):
    path: str
    possible_containers: Iterable[Path]


@dataclass
class UnificationSubtypingError(AeonError):
    expr: STerm
    subtype: SType
    suptype: SType
    msg: str = field(default_factory=lambda: "")


@dataclass
class UnificationFailedError(AeonError):
    name: str
    conflict1: SType
    conflict2: SType


@dataclass
class UnificationKindError(AeonError):
    term: STerm
    type: SType
    kind1: Kind
    kind2: Kind


@dataclass
class UnificationUnknownType(AeonError):
    term: STerm
