"""Offline training limits work with macOS's large reserved virtual mappings."""

from dataclasses import asdict
import json
import os
import subprocess
import sys

import pytest
import psutil

from aeon.synthesis.modules.amaze.resources import (
    MEMORY_LIMIT_BYTES,
    TrainingMemoryLimitExceeded,
    apply_worker_limits,
    wait_for_training,
)


class Limits:
    RLIMIT_AS = 9
    RLIMIT_CPU = 0
    RLIM_INFINITY = -1

    def __init__(self, limits):
        self.limits = limits.copy()

    def getrlimit(self, kind):
        return self.limits[kind]

    def setrlimit(self, kind, value):
        self.limits[kind] = value


def test_macos_uses_cpu_cap_without_applying_an_invalid_virtual_memory_cap():
    api = Limits({Limits.RLIMIT_AS: (-1, -1), Limits.RLIMIT_CPU: (-1, -1)})
    apply_worker_limits(30, platform="darwin", resource_api=api)
    assert api.limits[api.RLIMIT_AS] == (-1, -1)
    assert api.limits[api.RLIMIT_CPU] == (35, 35)


def test_linux_retains_kernel_caps_and_never_raises_inherited_limits():
    api = Limits({Limits.RLIMIT_AS: (MEMORY_LIMIT_BYTES // 2, MEMORY_LIMIT_BYTES), Limits.RLIMIT_CPU: (10, 10)})
    apply_worker_limits(30, platform="linux", resource_api=api)
    assert api.limits[api.RLIMIT_AS] == (MEMORY_LIMIT_BYTES // 2, MEMORY_LIMIT_BYTES // 2)
    assert api.limits[api.RLIMIT_CPU] == (10, 10)


def test_linux_applies_the_address_space_limit_when_unrestricted():
    api = Limits({Limits.RLIMIT_AS: (-1, -1), Limits.RLIMIT_CPU: (-1, -1)})
    apply_worker_limits(1, platform="linux", resource_api=api)
    assert api.limits[api.RLIMIT_AS] == (MEMORY_LIMIT_BYTES, MEMORY_LIMIT_BYTES)


def worker(code):
    return subprocess.Popen([sys.executable, "-c", code], start_new_session=os.name == "posix")


def test_resident_memory_guard_kills_and_reaps_a_real_worker():
    process = worker("import time; allocation = bytearray(32 * 1024**2); time.sleep(10)")
    with pytest.raises(TrainingMemoryLimitExceeded, match="resident-memory limit exhausted"):
        wait_for_training(process, 5, memory_limit=24 * 1024**2)
    assert process.returncode is not None


def test_wall_watchdog_still_kills_and_reaps_a_real_worker():
    process = worker("import time; time.sleep(10)")
    with pytest.raises(subprocess.TimeoutExpired):
        wait_for_training(process, 0.1)
    assert process.returncode is not None


def test_supervisor_preserves_worker_exit_status():
    process = worker("raise SystemExit(7)")
    assert wait_for_training(process, 5) == 7


def test_unavailable_memory_monitor_aborts_and_reaps_the_worker(monkeypatch):
    process = worker("import time; time.sleep(10)")

    def denied(self):
        raise psutil.AccessDenied(self.pid)

    monkeypatch.setattr(psutil.Process, "memory_info", denied)
    with pytest.raises(psutil.AccessDenied):
        wait_for_training(process, 5)
    assert process.returncode is not None


def test_limit_setup_errors_are_controlled_cli_failures(tmp_path, monkeypatch, capsys):
    from aeon.synthesis.modules.amaze import __main__ as cli
    from aeon.synthesis.modules.amaze.learning import Config

    def fail_setup(_budget):
        raise ValueError("kernel rejected limit")

    monkeypatch.setattr(cli, "apply_worker_limits", fail_setup)
    with pytest.raises(SystemExit) as failure:
        cli.main(["_train-worker", json.dumps(asdict(Config())), str(tmp_path / "absent.json")])
    assert failure.value.code == 2
    assert "AMaze training failed: kernel rejected limit" in capsys.readouterr().err
    assert not (tmp_path / "absent.json").exists()


def test_memory_aborted_training_preserves_an_existing_profile(tmp_path, monkeypatch, capsys):
    from aeon.synthesis.modules.amaze import __main__ as cli

    output = tmp_path / "profile.json"
    output.write_text("previous profile")

    def small_allowance(process, timeout):
        return wait_for_training(process, timeout, memory_limit=1)

    monkeypatch.setattr(cli, "wait_for_training", small_allowance)
    with pytest.raises(SystemExit) as failure:
        cli.main(["train-stdlib", "--output", str(output), "--budget", "1"])
    assert failure.value.code == 2
    assert "resident-memory limit exhausted" in capsys.readouterr().err
    assert output.read_text() == "previous profile"
    assert not list(tmp_path.glob(".amaze-*"))
