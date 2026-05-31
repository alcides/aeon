"""Source-location types — re-export of the Rust core
(``aeon-rs/src/location.rs``)."""

from aeon_rs import FileLocation as FileLocation
from aeon_rs import Location as Location
from aeon_rs import SynthesizedLocation as SynthesizedLocation

__all__ = ["FileLocation", "Location", "SynthesizedLocation"]
