from __future__ import annotations

import datetime
import sys

from loguru import logger


def levels_filter(levels):
    def filter(record):
        return record["level"].name in levels

    return filter


_CUSTOM_LEVELS = [
    ("TYPECHECKER", {"no": 35, "color": "<magenta>", "icon": "🔍"}),
    ("SYNTH_TYPE", {"no": 36, "color": "<magenta>"}),
    ("CONSTRAINT", {"no": 37, "color": "<cyan>", "icon": "🔒"}),
    ("SYNTHESIZER", {"no": 38, "color": "<red>"}),
    ("TIME", {"no": 39, "color": "<green>"}),
]


def _register_levels():
    for name, kwargs in _CUSTOM_LEVELS:
        try:
            logger.level(name, **kwargs)
        except (ValueError, TypeError):
            pass


# Eagerly register at import so library consumers (tests, LSP, benchmarks)
# can use these levels without first calling setup_logger().
_register_levels()


def setup_logger():
    _register_levels()
    logger.remove()
    return logger


def export_log(logs: list, export_file: bool = False, logfile_name: str = ""):
    if export_file:
        logfile = f"logs/{logfile_name}_{datetime.datetime.now().strftime('%Y_%m_%d %H_%M_%S')}.log"
        return logger.add(logfile, filter=levels_filter(logs))
    else:
        return logger.add(sys.stderr, filter=levels_filter(logs))
