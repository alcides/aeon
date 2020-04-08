from aeon.synthesis import se_safe
from aeon.automatic.individual import Individual

from aeon.automatic.initialization.full import full
from aeon.automatic.initialization.grow import grow

# =============================================================================
# Ramped: combination of both grow and full
def ramped(holes, size, depth):
    
    pop_full = full(holes, size // 2 + size % 2, depth)
    pop_grow = grow(holes, size // 2, depth)

    return pop_full + pop_grow