import json
import shutil
import subprocess
import sys

import pytest

from aeon.benchmarks.resources import (
    StoragePolicy,
    StorageLimitError,
    bounded_command,
    wait_with_limits,
    stop_process_group,
)


def test_preflight_reserves_headroom_for_all_workers(tmp_path, monkeypatch):
    policy = StoragePolicy(min_free_bytes=100, max_file_bytes=100, max_total_bytes=200)
    monkeypatch.setattr(shutil, "disk_usage", lambda path: type("Usage", (), {"free": 500})())
    policy.preflight(tmp_path, concurrency=2)
    with pytest.raises(StorageLimitError):
        policy.preflight(tmp_path, concurrency=3)


def test_output_exhaustion_is_infrastructure_failure_and_preserves_evidence(tmp_path):
    policy = StoragePolicy(min_free_bytes=0, max_file_bytes=4096, max_total_bytes=8192)
    output = tmp_path / "stdout"
    command = bounded_command([sys.executable, "-c", 'import sys; sys.stdout.buffer.write(b"x" * 1000000)'], policy)
    with output.open("wb") as stream:
        process = subprocess.Popen(command, stdout=stream, stderr=subprocess.DEVNULL, start_new_session=True)
        with pytest.raises(StorageLimitError) as error:
            wait_with_limits(process, tmp_path, [output], 5, policy)
    assert error.value.category == "infrastructure_error"
    assert process.poll() is not None
    assert 0 < output.stat().st_size <= policy.max_file_bytes
    # Results can be written and the raw log survives for diagnosis/resumption.
    result = tmp_path / "result.json"
    result.write_text(json.dumps({"status": error.value.category}))
    assert output.exists()


def test_low_disk_space_stops_an_active_trial(tmp_path, monkeypatch):
    process = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(20)"], start_new_session=True)
    monkeypatch.setattr(shutil, "disk_usage", lambda path: type("Usage", (), {"free": 0})())
    try:
        with pytest.raises(StorageLimitError):
            wait_with_limits(process, tmp_path, [], 5)
        assert process.poll() is not None
    finally:
        stop_process_group(process)


def test_external_timeout_remains_distinct(tmp_path):
    process = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(20)"], start_new_session=True)
    try:
        with pytest.raises(subprocess.TimeoutExpired):
            wait_with_limits(process, tmp_path, [], 0.1)
    finally:
        stop_process_group(process)


def test_successful_trial_is_not_reclassified(tmp_path):
    process = subprocess.Popen([sys.executable, "-c", "pass"], start_new_session=True)
    wait_with_limits(process, tmp_path, [], 5)
    assert process.returncode == 0


def test_combined_logs_have_a_total_limit(tmp_path):
    first, second = tmp_path / "stdout", tmp_path / "stderr"
    first.write_bytes(b"x" * 5000)
    second.write_bytes(b"x" * 5000)
    policy = StoragePolicy(min_free_bytes=0, max_file_bytes=10000, max_total_bytes=9000)
    with pytest.raises(StorageLimitError, match="Total trial output"):
        policy.check_outputs([first, second])


def test_child_artifact_limit_is_not_misclassified_as_backend_crash(tmp_path):
    artifact, stderr = tmp_path / "artifact", tmp_path / "stderr"
    policy = StoragePolicy(min_free_bytes=0, max_file_bytes=4096, max_total_bytes=8192)
    code = 'import sys; open(sys.argv[1], "wb").write(b"x" * 1000000)'
    command = bounded_command([sys.executable, "-c", code, str(artifact)], policy)
    with stderr.open("wb") as stream:
        process = subprocess.Popen(command, stderr=stream, start_new_session=True)
        with pytest.raises(StorageLimitError, match="artifact"):
            wait_with_limits(process, tmp_path, [stderr], 5, policy)
    assert artifact.stat().st_size <= policy.max_file_bytes
