import sys

from loguru import logger
import datetime


def levels_filter(levels):
    def filter(record):
        return record["level"].name in levels
    return filter


def setup_logger(logs: str = "", logfile_name: str = None):
    logger.level("TYPECHECKER", no=35, color="<magenta>", icon="🔍")
    logger.level("CONSTRAINT", no=36, color="<cyan>", icon="🔒")

    # Setup the logger
    logger.remove()
    #logger.add(sys.stderr, level="DEBUG")
    if not logfile_name:
        logger.add(sys.stderr, filter=levels_filter(logs))
    else:
        logfile = f"logs/{logfile_name}_{datetime.datetime.now()}.log"
        logger.add(logfile, filter=levels_filter(logs))

    return logger

