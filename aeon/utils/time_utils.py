from __future__ import annotations

from functools import wraps
from time import process_time
from time import perf_counter

from loguru import logger


def measure(func):

    @wraps(func)
    def _time_it(*args, **kwargs):
        start = int(round(process_time() * 1000))
        try:
            return func(*args, **kwargs)
        finally:
            end_ = int(round(process_time() * 1000)) - start
            if end_ > 1:
                end_s = end_ if end_ > 0 else 0
                print(f"Total execution time {func.__name__}: {end_s} ms", )

    return _time_it


class RecordTime:

    def __init__(self, name: str):
        self.name = name

    def __enter__(self):
        self.start = perf_counter()
        return self

    def __exit__(self, type, value, traceback):
        self.time = perf_counter() - self.start
        logger.log("TIME", f"[{self.name}] Time: {self.time:.3f} seconds")
