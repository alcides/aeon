from __future__ import annotations

from dataclasses import dataclass
from dataclasses import field

from aeon.core.multiplicity import Multiplicity, MOmega
from aeon.utils.name import Name
from aeon.core.types import Kind
from aeon.sugar.stypes import SType, STypeConstructor

from aeon.utils.location import Location, SynthesizedLocation


class STerm:
    loc: Location

    def __hash__(self) -> int:
        return str(self).__hash__()


@dataclass(frozen=True)
class SLiteral(STerm):
    value: object
    type: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        if type(self.value) is str:
            return f'"{self.value}"'
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, SLiteral) and self.value == other.value and self.type == other.type

    def __str__(self):
        if self.type == STypeConstructor(Name("String", 0)):
            return f'"{self.value}"'
        return f"{self.value}"


@dataclass(frozen=True)
class SVar(STerm):
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"{self.name}"

    def __repr__(self):
        return f"Var({self.name})"

    def __eq__(self, other):
        return isinstance(other, SVar) and self.name == other.name


@dataclass(frozen=True)
class SQualifiedVar(STerm):
    qualifier: str
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"{self.qualifier}.{self.name}"

    def __repr__(self):
        return f"QVar({self.qualifier}.{self.name})"


@dataclass(frozen=True)
class SAnnotation(STerm):
    expr: STerm
    type: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"({self.expr} : {self.type})"

    def __repr__(self):
        return f"({self.expr} : {self.type})"

    def __eq__(self, other):
        return isinstance(other, SAnnotation) and self.expr == other.expr


@dataclass(frozen=True)
class SHole(STerm):
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"?{self.name}"

    def __repr__(self):
        return f"Hole({self.name})"

    def __eq__(self, other):
        return isinstance(other, SHole) and self.name == other.name


@dataclass(frozen=True)
class SImplicitRefinementHole(STerm):
    """Placeholder inserted by elaboration when instantiating an
    ``SRefinementPolymorphism``.

    Always appears as the ``refinement`` field of ``SRefinementApplication``
    (and its core counterpart, ``RefinementApplication``). Solved by Horn
    inference downstream of elaboration, never by GP synthesis. Kept as a
    distinct ``STerm`` subclass — rather than a flag on ``SHole`` — so the
    two roles can't be confused at pattern-match sites: ``case SHole(...)``
    only fires for user-written or tactic-introduced holes.
    """

    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"?ρ{self.name}"

    def __repr__(self):
        return f"ImplicitRefinementHole({self.name})"

    def __eq__(self, other):
        return isinstance(other, SImplicitRefinementHole) and self.name == other.name


@dataclass(frozen=True)
class SInstanceHole(STerm):
    """Placeholder for an instance-implicit dictionary argument.

    Inserted by elaboration at a method-call site when the function expects an
    instance argument (``[C a] -> ...``). Carries the class type (e.g. ``Eq a``)
    with ``a`` possibly an unsolved unification variable. Resolved away in
    ``elaborate_remove_unification`` to a concrete ``SVar`` referencing the
    generated instance dictionary, so ``lower_to_core`` never sees it.
    """

    class_type: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"?inst[{self.class_type}]"

    def __repr__(self):
        return f"SInstanceHole({self.class_type!r})"

    def __eq__(self, other):
        return isinstance(other, SInstanceHole) and self.class_type == other.class_type


@dataclass(frozen=True)
class SBy(STerm):
    """Lean-style ``by`` tactic script (no ``end``).

    Single tactic: ``by TACTIC``. Several tactics use parentheses so ``;`` does not
    clash with ``def ... = ... ;``: ``by (TACTIC; TACTIC; ...)``.
    """

    steps: tuple[str, ...]
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return "by " + "; ".join(self.steps)

    def __repr__(self):
        return f"SBy({self.steps!r})"

    def __eq__(self, other):
        return isinstance(other, SBy) and self.steps == other.steps


@dataclass(frozen=True)
class SApplication(STerm):
    fun: STerm
    arg: STerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return f"({self.fun} {self.arg})"

    def __eq__(self, other):
        return isinstance(other, SApplication) and self.fun == other.fun and self.arg == other.arg

    def __str__(self):
        return f"({self.fun} {self.arg})"


@dataclass(frozen=True)
class SAbstraction(STerm):
    var_name: Name
    body: STerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"(fun {self.var_name} => {self.body})"

    def __eq__(self, other):
        return isinstance(other, SAbstraction) and self.var_name == other.var_name and self.body == other.body


@dataclass(frozen=True)
class SLet(STerm):
    var_name: Name
    var_value: STerm
    body: STerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))
    multiplicity: Multiplicity = MOmega

    def __str__(self):
        prefix = "" if self.multiplicity is MOmega else f"{self.multiplicity} "
        return f"(let {prefix}{self.var_name} = {self.var_value} in\n\t{self.body})"

    def __eq__(self, other):
        return (
            isinstance(other, SLet)
            and self.var_name == other.var_name
            and self.var_value == other.var_value
            and self.body == other.body
            and self.multiplicity is other.multiplicity
        )


@dataclass(frozen=True)
class SRec(STerm):
    var_name: Name
    var_type: SType
    var_value: STerm
    body: STerm
    decreasing_by: tuple[STerm, ...] = field(default_factory=tuple)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))
    multiplicity: Multiplicity = MOmega

    def __repr__(self):
        return str(self)

    def __str__(self):
        prefix = "" if self.multiplicity is MOmega else f"{self.multiplicity} "
        return "(let {}{} : {} = {} in\n\t{})".format(
            prefix,
            self.var_name,
            self.var_type,
            self.var_value,
            self.body,
        )

    def __eq__(self, other):
        return (
            isinstance(other, SRec)
            and self.var_name == other.var_name
            and self.var_type == other.var_type
            and self.var_value == other.var_value
            and self.body == other.body
            and self.decreasing_by == other.decreasing_by
            and self.multiplicity is other.multiplicity
        )


@dataclass(frozen=True)
class SIf(STerm):
    cond: STerm
    then: STerm
    otherwise: STerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"(if {self.cond} then {self.then} else {self.otherwise})"

    def __eq__(self, other):
        return (
            isinstance(other, SIf)
            and self.cond == other.cond
            and self.then == other.then
            and self.otherwise == other.otherwise
        )


@dataclass(frozen=True)
class SAnonConstructor(STerm):
    name: str
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f".{self.name}"

    def __repr__(self):
        return f"AnonCtor(.{self.name})"

    def __eq__(self, other):
        return isinstance(other, SAnonConstructor) and self.name == other.name


@dataclass(frozen=True)
class SMethodSelector(STerm):
    """Deferred, type-directed method lookup (issue #27, *method call* syntax).

    The surface form ``receiver.method`` parses to
    ``SApplication(SMethodSelector(method), receiver)``. Keeping the selector a
    *leaf* (it carries only the method name, never the receiver) means every
    ``SApplication``-recursing pass already walks into the receiver for free, so
    no desugar/bind/substitution pass needs a bespoke case — only elaboration,
    which has the receiver's type and rewrites the node to a plain reference to
    the resolved ``Type.method`` function applied to the receiver.

    A selector never stands alone: it is always the ``fun`` of the application
    the parser builds around it.
    """

    method: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f".{self.method}"

    def __repr__(self):
        return f"MethodSelector(.{self.method})"

    def __eq__(self, other):
        return isinstance(other, SMethodSelector) and self.method == other.method


@dataclass(frozen=True)
class SMatchBranch:
    constructor: Name
    binders: list[Name]
    body: STerm
    qualifier: str | None = None
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        binders = " ".join(str(b) for b in self.binders)
        prefix = f"{self.qualifier}." if self.qualifier else ""
        if binders:
            return f"| {prefix}{self.constructor} {binders} => {self.body}"
        return f"| {prefix}{self.constructor} => {self.body}"


@dataclass(frozen=True)
class SMatch(STerm):
    scrutinee: STerm
    branches: list[SMatchBranch]
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        branches_str = "\n".join(str(b) for b in self.branches)
        return f"(match {self.scrutinee} with\n{branches_str})"

    def __repr__(self):
        return str(self)


@dataclass(frozen=True)
class STypeAbstraction(STerm):
    name: Name
    kind: Kind
    body: STerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"ƛ{self.name}:{self.kind}.({self.body})"


@dataclass(frozen=True)
class SRefinementAbstraction(STerm):
    """Binds a refinement parameter ρ whose sort is the full (possibly n-ary)
    predicate type ρ : d1 -> ... -> Bool."""

    name: Name
    sort: SType
    body: STerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"Λ<{self.name}:{self.sort}>=> ({self.body})"


@dataclass()  # frozen=True
class STypeApplication(STerm):
    body: STerm
    type: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"({self.body})[{self.type}]"


@dataclass(frozen=True)
class SRefinementApplication(STerm):
    body: STerm
    refinement: STerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"({self.body})[{self.refinement}]"


class Node:
    pass


@dataclass
class ImportAe(Node):
    module_path: str  # e.g. "Math" or "Math.Basic"
    selected_names: list[str] = field(default_factory=list)  # empty = all (qualified access)
    is_open: bool = False  # True for `open Math`
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    @property
    def file_path(self) -> str:
        """Convert module path to filesystem path: Math -> Math.ae, Math.Basic -> Math/Basic.ae"""
        return self.module_path.replace(".", "/") + ".ae"

    @property
    def module_name(self) -> str:
        """The top-level module name used as qualifier, e.g. 'Math' from 'Math.Basic'."""
        return self.module_path.split(".")[0]

    def __str__(self):
        if self.is_open:
            return f"open {self.module_path};"
        elif self.selected_names:
            names = ", ".join(self.selected_names)
            return f"import {self.module_path} ({names});"
        else:
            return f"import {self.module_path};"


@dataclass
class TypeDecl(Node):
    name: Name
    args: list[Name] = field(default_factory=list)
    rforalls: list[tuple[Name, SType]] = field(default_factory=list)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        args = " ".join(str(arg) for arg in self.args)
        rfs = " ".join(f"forall <{n}:{s} -> Bool>" for (n, s) in self.rforalls)
        head = f"type {self.name}"
        if args:
            head += f" {args}"
        if rfs:
            head += f" {rfs}"
        return f"{head};"


@dataclass
class InductiveDecl(Node):
    """Datatype declaration. ``rforalls`` are abstract refinement parameters (Liquid Haskell ``data T a <p :: a -> Bool>``)."""

    name: Name
    args: list[Name] = field(default_factory=list)
    rforalls: list[tuple[Name, SType]] = field(default_factory=list)
    constructors: list[Definition] = field(default_factory=list)
    measures: list[Definition] = field(default_factory=list)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __post_init__(self):
        assert isinstance(self.name, Name)

        for aname in self.args:
            assert isinstance(aname, Name)

    def __str__(self):
        args = " ".join(str(arg) for arg in self.args)
        rfs = " ".join(f"forall <{n}:{s} -> Bool>" for (n, s) in self.rforalls)
        constructors = " ".join(f"| {cons}" for (cons) in self.constructors)
        measures = " ".join(f"+ {dec}" for dec in self.measures)
        head = f"inductive {self.name}"
        if args:
            head += f" {args}"
        if rfs:
            head += f" {rfs}"
        return f"{head} {constructors} {measures}"


@dataclass
class Decorator(Node):
    name: Name
    macro_args: list[STerm]
    named_args: dict[Name, STerm] = field(default_factory=dict)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        macro_args = ", ".join([f"{term}" for term in self.macro_args])
        named_args = ", ".join([f"{n}={t}" for n, t in self.named_args.items()])
        all_args = ", ".join(filter(None, [macro_args, named_args]))
        return f"@{self.name}({all_args})"


@dataclass
class Definition(Node):
    name: Name
    foralls: list[tuple[Name, Kind]]
    args: list[tuple[Name, SType]]
    type: SType
    body: STerm
    decorators: list[Decorator] = field(default_factory=list)
    rforalls: list[tuple[Name, SType]] = field(default_factory=list)
    decreasing_by: list[STerm] = field(default_factory=list)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))
    # Parallel to ``args``: the QTT multiplicity declared for each parameter.
    # Empty tuple ⇔ all parameters default to ``MOmega`` (the value used by
    # callers that don't track multiplicities yet).
    arg_multiplicities: tuple[Multiplicity, ...] = field(default_factory=tuple)
    # Parallel to ``args``: True marks an instance-implicit parameter (typeclass
    # dictionary / Lean ``[C a]``). Empty tuple ⇔ no instance-implicit params.
    instance_flags: tuple[bool, ...] = field(default_factory=tuple)

    def multiplicity_of(self, i: int) -> Multiplicity:
        if i < len(self.arg_multiplicities):
            return self.arg_multiplicities[i]
        return MOmega

    def is_instance_arg(self, i: int) -> bool:
        if i < len(self.instance_flags):
            return self.instance_flags[i]
        return False

    def __post_init__(self):
        assert isinstance(self.type, SType)

    def __str__(self):
        if not self.args:
            return f"def {self.name} : {self.type} = {self.body};"
        else:
            args = ", ".join(
                [
                    f"{'' if self.multiplicity_of(i) is MOmega else str(self.multiplicity_of(i)) + ' '}{n}:{t}"
                    for i, (n, t) in enumerate(self.args)
                ]
            )
            foralls = " ".join([f"∀{n}:{k}" for (n, k) in self.foralls])
            rforalls = " ".join([f"∀<{n}:{s} -> Bool>" for (n, s) in self.rforalls])
            sep = " " if (foralls or rforalls) else ""
            return f"def {self.name}{sep}{foralls}{sep}{rforalls} {args} : {self.type} {{\n {self.body} \n}}"


@dataclass
class ClassMethod(Node):
    """A method declared inside a ``class`` body.

    ``args`` are the explicit value parameters (Lean/``def`` style); ``type`` is the
    return type. ``default`` is the optional default body used when an instance omits
    the method. A method's ``type`` (and any refinement in it) may reference sibling
    methods by their bare name — these become refinement *laws* verified per instance.
    """

    name: Name
    args: list[tuple[Name, SType]]
    type: SType
    default: STerm | None = None
    arg_multiplicities: tuple[Multiplicity, ...] = field(default_factory=tuple)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def multiplicity_of(self, i: int) -> Multiplicity:
        if i < len(self.arg_multiplicities):
            return self.arg_multiplicities[i]
        return MOmega


@dataclass
class ClassDecl(Node):
    """A Lean-style typeclass declaration.

    ``type_params`` are the class type parameters (e.g. ``a`` in ``class Eq (a : B)``).
    ``supers`` are superclass constraints from ``extends`` (each an ``SType`` like
    ``Eq a``). ``methods`` are the class members.
    """

    name: Name
    type_params: list[tuple[Name, Kind]] = field(default_factory=list)
    supers: list[SType] = field(default_factory=list)
    methods: list[ClassMethod] = field(default_factory=list)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))


@dataclass
class InstanceMethod(Node):
    """A method definition inside an ``instance`` body: ``name args := body``."""

    name: Name
    args: list[tuple[Name, SType]]
    body: STerm
    arg_multiplicities: tuple[Multiplicity, ...] = field(default_factory=tuple)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def multiplicity_of(self, i: int) -> Multiplicity:
        if i < len(self.arg_multiplicities):
            return self.arg_multiplicities[i]
        return MOmega


@dataclass
class InstanceDecl(Node):
    """A Lean-style instance declaration.

    ``class_name`` is the class being instantiated; ``type_args`` are the type
    arguments (e.g. ``Int`` in ``instance Eq Int``). ``constraints`` are instance-implicit
    requirements from ``[Eq a]`` style binders (each an ``SType`` like ``Eq a``).
    ``name`` is the optional user-supplied dictionary name.
    """

    class_name: Name
    type_args: list[SType] = field(default_factory=list)
    constraints: list[SType] = field(default_factory=list)
    methods: list[InstanceMethod] = field(default_factory=list)
    name: Name | None = None
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))


@dataclass
class Program(Node):
    imports: list[ImportAe]
    type_decls: list[TypeDecl]
    inductive_decls: list[InductiveDecl]
    definitions: list[Definition]
    class_decls: list[ClassDecl] = field(default_factory=list)
    instance_decls: list[InstanceDecl] = field(default_factory=list)

    def __str__(self):
        imps = "\n".join([str(td) for td in self.imports])
        decls = "\n".join([str(td) for td in self.type_decls])
        inductives = "\n".join([str(td) for td in self.inductive_decls])
        defs = "\n".join([str(d) for d in self.definitions])
        return f"{imps}\n{decls}\n{inductives}\n{defs}"
