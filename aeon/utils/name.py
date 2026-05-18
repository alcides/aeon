"""Re-export Name from the Rust core (aeon_rs); expose `fresh_counter`."""

from aeon_rs import FreshCounter as _FreshCounter
from aeon_rs import Name as Name

fresh_counter = _FreshCounter()
