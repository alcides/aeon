"""Use solver resource units instead of milliseconds in deterministic runs."""

from aeon.compilation.session import current_session


def set_solver_limits(solver, timeout_ms: int) -> None:
    limit = current_session().options.smt_rlimit
    if limit is None:
        solver.set(timeout=timeout_ms)
    else:
        solver.set(timeout=0, rlimit=limit, random_seed=0)
