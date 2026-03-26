from __future__ import annotations

import datetime
import sys

from loguru import logger


def levels_filter(levels):
    def filter(record):
        return record["level"].name in levels

    return filter


def setup_logger():
    for name, kwargs in [
        ("TYPECHECKER", {"no": 35, "color": "<magenta>", "icon": "🔍"}),
        ("SYNTH_TYPE", {"no": 36, "color": "<magenta>"}),
        ("CONSTRAINT", {"no": 37, "color": "<cyan>", "icon": "🔒"}),
        ("SYNTHESIZER", {"no": 38, "color": "<red>"}),
        ("TIME", {"no": 39, "color": "<green>"}),
    ]:
        try:
            logger.level(name, **kwargs)
        except ValueError:
            pass

    # Setup the logger
    logger.remove()
    # logger.add(sys.stderr, level="DEBUG")
    return logger


def export_log(logs: list, export_file: bool = False, logfile_name: str = ""):
    if export_file:
        logfile = f"logs/{logfile_name}_{datetime.datetime.now().strftime('%Y_%m_%d %H_%M_%S')}.log"
        return logger.add(logfile, filter=levels_filter(logs))
    else:
        return logger.add(sys.stderr, filter=levels_filter(logs))
