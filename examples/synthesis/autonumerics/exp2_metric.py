"""Native helpers for the Aeon AutoNumerics-Zero exp2 example.

Implements the evaluation metric of Real, Rossini, de Souza, Garg, Firsching,
Le, Chen, Verghese, Cubuk & Park, "AutoNumerics-Zero: Automated Discovery of
State-of-the-Art Mathematical Functions" (ICML 2026; arXiv:2312.08472; Gold,
2026 Human-Competitive "HUMIES" awards; code:
github.com/google-deepmind/autonumerics_zero): the paper searches, with
symbolic regression over {+, -, *, /}, float constants and the input x, for
finite-precision programs approximating the exponential 2**x on the domain
(0, 1] (extendable to all reals via standard range reduction), minimising the
maximum relative error together with the number of operations.

Its headline result is a 10-operation program ("f10", Figure 11 of the paper)
whose maximum relative error is proven below ~5.4e-15 -- about 14 significant
figures, beating previously known same-size approximations by more than 6
orders of magnitude.

Everything here is a plain-Python reimplementation of the *metric* only.  The
paper proves its error bounds with interval arithmetic (IBEX) and additionally
optimises float32 speed on hardware via JAX/XLA; neither is reproduced.
Errors below are measured by sampling a dense float64 grid, which is fine for
a demo but is a measurement, not a proof.
"""

import math

# Per-candidate fitness grid.  Kept modest because free-form candidates are
# interpreted Aeon closures, so every extra point costs an interpreter call
# inside the synthesiser's inner loop.
FITNESS_POINTS = 128

# Verification grid for reporting the error of known programs: dense uniform
# samples of (0, 1] plus log-spaced points down to 1e-8, probing the x -> 0+
# end of the domain where the reciprocal-based programs are most delicate.
DENSE_POINTS = 20000
DENSE_LOG_POINTS = 2000

# Score for candidates that crash (division by zero), overflow to inf, or
# produce nan: large enough to dominate any real error, finite so the
# genetic-programming backend can still rank individuals.
PENALTY = 1.0e9


def _uniform_grid(n):
    return [i / n for i in range(1, n + 1)]


def _dense_grid():
    log_pts = [10.0 ** (-8.0 + 8.0 * i / DENSE_LOG_POINTS) for i in range(DENSE_LOG_POINTS)]
    return log_pts + _uniform_grid(DENSE_POINTS)


def max_rel_error(func, grid=None):
    """Maximum relative error of candidate ``func`` against 2**x on (0, 1].

    ``func`` is a candidate from open-ended search: it may divide by zero,
    overflow, or return nan, so failures score PENALTY (steering the search
    away) instead of crashing the synthesiser.  The relative-error denominator
    2**x lies in (1, 2] on this domain, so the metric itself is total.
    """
    if grid is None:
        grid = _uniform_grid(FITNESS_POINTS)
    worst = 0.0
    for x in grid:
        try:
            y = float(func(x))
        except (ArithmeticError, ValueError):
            return PENALTY
        if not math.isfinite(y):
            return PENALTY
        target = 2.0**x
        err = abs(y - target) / target
        if err > worst:
            worst = err
    return worst


def mre_dense(func):
    """``max_rel_error`` on the dense verification grid (report-quality)."""
    return max_rel_error(func, _dense_grid())


def pade_mre(a, b, c):
    """Fitness of the fixed [0/1] Pade skeleton  a*a / (1 + b*x) + c.

    This is the shape of the paper's evolved 3-operation program f3 (Figure
    11) -- a reciprocal plus a constant -- renormalised so the optimal
    coefficients (~1.56, ~-0.29, ~-1.44) fit inside the +-5.12 search box of
    Aeon's ``ng_float`` synthesizer. The numerator is parameterised as ``a*a``
    (a constant fold: at runtime the program is still 3 operations): keeping
    it positive removes a spurious sign-symmetric local optimum with a
    negative numerator -- approximating the increasing 2^x needs an
    increasing reciprocal branch.
    Evaluated natively (no Aeon interpreter in the loop), so the full fitness
    grid costs microseconds per candidate. A candidate whose pole 1 + b*x
    hits zero on the grid scores PENALTY via ``max_rel_error``'s guard.
    """
    return max_rel_error(lambda x: (a * a) / (1.0 + b * x) + c)


def pade_mre_dense(a, b, c):
    """Dense-grid error of the Pade skeleton, for reporting."""
    return mre_dense(lambda x: (a * a) / (1.0 + b * x) + c)
