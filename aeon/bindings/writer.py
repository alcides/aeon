"""Helpers for ``libraries/Writer.ae``."""

from __future__ import annotations


def write_payload(data, writer):
    writer.write(data)
    # Track cumulative bytes on the handle for runtime debugging; refinements
    # are established by posts, not by reading this attribute.
    written = getattr(writer, "_aeon_bytes_written", 0) + len(data)
    setattr(writer, "_aeon_bytes_written", written)
    return writer
