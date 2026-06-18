from __future__ import annotations

import sqlite3

from aeon.bindings.binding_utils import curried


@curried
def read_all(path, sql):
    """Open ``path``, run a read-only ``sql`` query, and return all rows.

    The connection is opened and closed entirely inside this helper, so no
    handle escapes to Aeon — there is nothing for a caller to leak. Returns a
    ``list`` of row tuples (``len`` is the row count).
    """
    conn = sqlite3.connect(path)
    try:
        return conn.execute(sql).fetchall()
    finally:
        conn.close()
