"""Helpers for ``libraries/Reader.ae``."""

from __future__ import annotations


def read_step(reader):
    """Read one byte; return ``(code, reader)`` with ``code == -1`` at EOF."""
    data = reader.read(1)
    if not data:
        return (-1, reader)
    return (data[0], reader)
