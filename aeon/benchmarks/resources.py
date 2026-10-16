"""Storage safeguards for external synthesis evaluation processes."""

from __future__ import annotations

from dataclasses import dataclass
import os
import errno
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time
from typing import Sequence

MIB = 1024 * 1024


class StorageLimitError(RuntimeError):
    """An evaluation infrastructure failure, never a synthesis no-solution."""

    category = "infrastructure_error"


@dataclass(frozen=True)
class StoragePolicy:
    min_free_bytes: int = 64 * MIB
    max_file_bytes: int = 16 * MIB
    max_total_bytes: int = 32 * MIB

    def __post_init__(self):
        if self.min_free_bytes < 0 or self.max_file_bytes <= 0 or self.max_total_bytes <= 0:
            raise ValueError("Storage thresholds must be positive (free-space floor may be zero)")

    def preflight(self, directory: Path, concurrency: int = 1) -> None:
        if concurrency < 1:
            raise ValueError("Concurrency must be positive")
        needed = self.min_free_bytes + concurrency * self.max_total_bytes
        available = shutil.disk_usage(directory).free
        if available < needed:
            raise StorageLimitError(f"Insufficient disk space: {available} bytes free, {needed} required")

    def check_outputs(self, paths: Sequence[Path]) -> None:
        sizes = [path.stat().st_size for path in paths if path.exists()]
        if any(size >= self.max_file_bytes for size in sizes):
            raise StorageLimitError(f"Per-file output limit reached ({self.max_file_bytes} bytes)")
        if sum(sizes) >= self.max_total_bytes:
            raise StorageLimitError(f"Total trial output limit reached ({self.max_total_bytes} bytes)")


def stop_process_group(process: subprocess.Popen) -> None:
    """Stop a dedicated session, without risking the caller's process group."""
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        if process.poll() is None:
            process.kill()
    process.wait()


def wait_with_limits(
    process: subprocess.Popen,
    directory: Path,
    paths: Sequence[Path],
    timeout_s: float,
    policy: StoragePolicy = StoragePolicy(),
    poll_s: float = 0.1,
) -> None:
    """Monitor disk and output while preserving a distinct external timeout.

    Launch with start_new_session=True. A storage violation kills that process
    group and raises StorageLimitError. TimeoutExpired is left to the caller's
    existing timeout cleanup so it remains a distinct recorded outcome.
    """
    if timeout_s <= 0 or poll_s <= 0:
        raise ValueError("Timeout and polling interval must be positive")
    deadline = time.monotonic() + timeout_s
    while True:
        try:
            policy.check_outputs(paths)
            if process.poll() is not None:
                # The inherited limit also covers child-created artifacts,
                # which need not be among the four captured log paths.
                if process.returncode in (-signal.SIGXFSZ, 128 + signal.SIGXFSZ):
                    raise StorageLimitError("Child process exceeded its inherited file-size limit")
                if process.returncode:
                    for path in paths:
                        if path.name.endswith("stderr") and path.exists():
                            with path.open("rb") as stream:
                                stream.seek(max(0, path.stat().st_size - 4096))
                                tail = stream.read().decode(errors="replace")
                            if f"[Errno {errno.EFBIG}]" in tail and "File too large" in tail:
                                raise StorageLimitError("Child artifact exceeded its inherited file-size limit")
                return
            if shutil.disk_usage(directory).free < policy.min_free_bytes:
                raise StorageLimitError("Free disk space dropped below the trial safety floor")
        except StorageLimitError:
            stop_process_group(process)
            raise
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(process.args, timeout_s)
        try:
            process.wait(timeout=min(poll_s, remaining))
        except subprocess.TimeoutExpired:
            pass


def bounded_command(command: Sequence[str], policy: StoragePolicy = StoragePolicy()) -> list[str]:
    """Set an inherited kernel file-size limit before exec, without preexec_fn."""
    if not command:
        raise ValueError("A command is required")
    wrapper = Path(__file__).with_name("limit_exec.py")
    return [sys.executable, str(wrapper), str(policy.max_file_bytes), *command]
