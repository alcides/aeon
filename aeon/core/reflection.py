"""First-order equations for exhaustive datatype eliminators.

The internal tester/selector symbols are interpreted by SMT's datatype theory,
not assumed as axioms. Handlers are only evaluated under their constructor guard.
"""

from aeon.core.liquid import LiquidApp, LiquidTerm
from aeon.core.terms import Abstraction, Annotation, Application, RefinementApplication, Term, TypeApplication, Var
from aeon.utils.name import Name
from aeon.verification.constructor_registry import get_constructor_fields, get_constructor_groups, get_constructor_order


def datatype_operation(name: Name) -> tuple[str, str, int] | None:
    parts = name.name.split(":")
    if name.id == 0 and len(parts) == 3 and parts[0] in {"$is", "$field"}:
        return parts[0], parts[1], int(parts[2])
    return None


def liquefy_eliminator(term: Application) -> LiquidTerm | None:
    # Local import avoids the substitutions -> reflection -> substitutions cycle.
    from aeon.core.substitutions import liquefy, substitution_in_liquid

    args: list[Term] = []
    head: Term = term
    while isinstance(head, (Application, TypeApplication, RefinementApplication, Annotation)):
        if isinstance(head, Application):
            args.insert(0, head.arg)
            head = head.fun
        else:
            head = head.expr if isinstance(head, Annotation) else head.body
    if not isinstance(head, Var):
        return None
    datatype = next((t for t in get_constructor_groups() if head.name.name == t + "_rec"), None)
    if datatype is None:
        return None
    constructors = get_constructor_order(datatype) or []
    if len(args) != len(constructors) + 1:
        return None
    scrutinee = liquefy(args[0])
    if scrutinee is None:
        return None
    branches: list[tuple[LiquidTerm, LiquidTerm]] = []
    for ctor, handler in zip(constructors, args[1:]):
        binders: list[Name] = []
        for _ in get_constructor_fields(ctor) or []:
            while isinstance(handler, Annotation):
                handler = handler.expr
            if not isinstance(handler, Abstraction):
                return None
            binders.append(handler.var_name)
            handler = handler.body
        body = liquefy(handler)
        if body is None:
            return None
        work = [body]
        while work:
            node = work.pop()
            if isinstance(node, LiquidApp):
                # A function-valued field cannot be applied by the first-order
                # selector encoding (e.g. a delayed computation).
                if node.fun in binders:
                    return None
                work.extend(node.args)
        for i, binder in enumerate(binders):
            selector = LiquidApp(Name(f"$field:{ctor}:{i}", 0), [scrutinee])
            body = substitution_in_liquid(body, selector, binder)
        branches.append((LiquidApp(Name(f"$is:{ctor}:0", 0), [scrutinee]), body))
    if not branches:
        return None
    result = branches[-1][1]
    for guard, body in reversed(branches[:-1]):
        result = LiquidApp(Name("ite", 0), [guard, body, result])
    return result
