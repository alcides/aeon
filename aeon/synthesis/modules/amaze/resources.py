"""Contain offline training without mistaking reserved address space for RAM."""

from __future__ import annotations

import math
import os
import signal
import subprocess
import sys
import time

import psutil

MEMORY_LIMIT_BYTES = 4 * 1024**3
POLL_INTERVAL = 0.05


class TrainingMemoryLimitExceeded(RuntimeError):
    pass


def _lower_limit(resource_api, kind: int, requested: int) -> None:
    soft, hard = resource_api.getrlimit(kind)
    finite = [value for value in (soft, hard) if value != resource_api.RLIM_INFINITY]
    target = min(requested, *finite) if finite else requested
    resource_api.setrlimit(kind, (target, target))


def apply_worker_limits(budget: float, *, platform: str | None = None, resource_api=None) -> None:
    """Keep Linux's hard VM cap and POSIX CPU cap without raising inherited limits.

    macOS reserves much more VM than the process actually occupies. Its RAM
    protection comes from the parent's RSS watchdog instead of RLIMIT_AS.
    """
    platform = sys.platform if platform is None else platform
    if platform == "win32":
        return
    if resource_api is None:
        import resource as resource_api
    if platform.startswith("linux"):
        _lower_limit(resource_api, resource_api.RLIMIT_AS, MEMORY_LIMIT_BYTES)
    _lower_limit(resource_api, resource_api.RLIMIT_CPU, math.ceil(budget) + 5)


def terminate_training(process: subprocess.Popen) -> None:
    """Kill and reap the owned training worker and its POSIX process group."""
    if process.poll() is None:
        try:
            if os.name == "posix":
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    process.kill()
            else:
                process.kill()
        except ProcessLookupError:
            pass
    process.wait()


def wait_for_training(process: subprocess.Popen, timeout: float, *, memory_limit: int = MEMORY_LIMIT_BYTES) -> int:
    """Watch the worker's resident bytes from outside its interpreter/GIL.

    This is sampled protection: RSS can overshoot between checks. Linux also
    has the worker's hard address-space cap. Monitoring failures abort training
    instead of silently running without the memory guard.
    """
    deadline = time.monotonic() + timeout
    try:
        try:
            worker = psutil.Process(process.pid)
        except psutil.NoSuchProcess:
            return process.wait()
        while True:
            code = process.poll()
            if code is not None:
                return code
            try:
                resident = worker.memory_info().rss
            except psutil.NoSuchProcess:
                return process.wait()
            if resident > memory_limit:
                raise TrainingMemoryLimitExceeded(
                    f"AMaze offline resident-memory limit exhausted ({resident} > {memory_limit} bytes)"
                )
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise subprocess.TimeoutExpired(process.args, timeout)
            try:
                return process.wait(timeout=min(POLL_INTERVAL, remaining))
            except subprocess.TimeoutExpired:
                pass
    except BaseException:
        terminate_training(process)
        raise
