"""A bounded RPC worker contains generation, validation, and candidate execution."""

import multiprocess as mp
from aeon.synthesis.budgets import (
    EvaluationWatchdogExpired,
    OpcodeBudgetExceeded,
    OpcodeMeter,
    current_budget,
    raise_watchdog,
    unmetered,
)


class WorkerTimeout(Exception):
    pass


class WorkerError(Exception):
    pass


class WorkerResourceLimit(WorkerError):
    pass


def _serve(connection, operations, policy=None):
    import sys

    sys.settrace(None)
    search_meter = OpcodeMeter(policy.opcodes) if policy else None
    try:
        while True:
            message = connection.recv()
            if message is None:
                return
            operation, argument = message
            try:
                if policy is None:
                    value = operations[operation](argument)
                else:
                    meter = (
                        search_meter
                        if operation in {"next", "validate", "domain"}
                        else OpcodeMeter(policy.evaluation_opcodes, include_foreign=True)
                    )
                    with meter.measure():
                        value = operations[operation](argument)
                connection.send((True, value))
            except OpcodeBudgetExceeded:
                connection.send((False, "opcode budget exhausted"))
            except EvaluationWatchdogExpired as exc:
                connection.send((False, "fatal_watchdog: " + str(exc)))
            except Exception as exc:
                connection.send((False, f"{type(exc).__name__}: {exc}"))
    except (EOFError, BrokenPipeError):
        pass
    finally:
        connection.close()


class Worker:
    @unmetered
    def __init__(self, operations):
        self.policy = current_budget()
        context = mp.get_context("fork")
        self.connection, child = context.Pipe()
        self.process = context.Process(target=_serve, args=(child, operations, self.policy), daemon=True)
        self.process.start()
        child.close()

    @unmetered
    def call(self, operation, argument, timeout):
        if self.policy is not None:
            timeout = 60.0
        if timeout <= 0:
            raise WorkerTimeout()
        try:
            self.connection.send((operation, argument))
            if not self.connection.poll(timeout):
                if self.policy is not None:
                    raise_watchdog("Worker exceeded its deterministic-run safety watchdog")
                raise WorkerTimeout()
            success, value = self.connection.recv()
        except (EOFError, BrokenPipeError, OSError) as exc:
            if self.policy is not None:
                raise_watchdog("Worker exited without a deterministic result")
            raise WorkerError("Noisy worker exited") from exc
        if not success:
            if value.startswith("fatal_watchdog: "):
                raise_watchdog(value.removeprefix("fatal_watchdog: "))
            if value == "opcode budget exhausted":
                raise WorkerResourceLimit(value)
            raise WorkerError(value)
        return value

    @unmetered
    def close(self):
        self.connection.close()
        if self.process.is_alive():
            self.process.terminate()
        self.process.join(timeout=0.05)
        if self.process.is_alive():
            self.process.kill()
            # SIGKILL cannot be ignored, but exit/reaping is not instantaneous
            # on a busy host. Do not return while the child is still present.
            self.process.join()
