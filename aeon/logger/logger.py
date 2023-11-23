from __future__ import annotations

import datetime
import sys

from loguru import logger


def levels_filter(levels):
    def filter(record):
        return record["level"].name in levels

    return filter


def setup_logger():
    logger.level("TYPECHECKER", no=35, color="<magenta>")
    logger.level("CONSTRAINT", no=36, color="<cyan>")
    logger.level("SYNTHESIZER", no=37, color="<red>")

    # Setup the logger
    logger.remove()
    logger.add(sys.stderr, level="DEBUG")
    return logger


def export_log(logs: list, export_file: bool = False, logfile_name: str | None = None):
    if export_file:
        logfile = f"logs/{logfile_name}_{datetime.datetime.now()}.log"
        return logger.add(logfile, filter=levels_filter(logs))
    else:
        return logger.add(sys.stderr, filter=levels_filter(logs))
