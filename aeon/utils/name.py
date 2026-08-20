"""Name and FreshCounter — re-export of the Rust core
(``aeon-rs/src/name.rs``)."""

from aeon_rs import FreshCounter as FreshCounter
from aeon_rs import Name as Name

fresh_counter = FreshCounter()

__all__ = ["FreshCounter", "Name", "fresh_counter"]
