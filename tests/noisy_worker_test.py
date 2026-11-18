"""Worker cleanup must finish even when process exit is delayed."""

from unittest.mock import Mock

from aeon.synthesis.modules.noisy.worker import Worker


def test_close_reaps_a_child_with_delayed_exit():
    worker = Worker.__new__(Worker)
    worker.connection = Mock()
    worker.process = process = Mock()
    process.is_alive.return_value = True

    def join(timeout=None):
        # Emulate a loaded host where SIGKILL has been sent but the child takes
        # longer than the old 50 ms cleanup allowance to exit and be reaped.
        if process.kill.called and (timeout is None or timeout >= 0.2):
            process.is_alive.return_value = False

    process.join.side_effect = join
    worker.close()
    assert not process.is_alive(), "close returned before the killed child was reaped"
    worker.connection.close.assert_called_once_with()
