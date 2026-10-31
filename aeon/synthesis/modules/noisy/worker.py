"""A bounded RPC worker contains generation, validation, and candidate execution."""

import multiprocess as mp


class WorkerTimeout(Exception):
    pass


class WorkerError(Exception):
    pass


def _serve(connection, operations):
    try:
        while True:
            message = connection.recv()
            if message is None:
                return
            operation, argument = message
            try:
                connection.send((True, operations[operation](argument)))
            except Exception as exc:
                connection.send((False, f"{type(exc).__name__}: {exc}"))
    except (EOFError, BrokenPipeError):
        pass
    finally:
        connection.close()


class Worker:
    def __init__(self, operations):
        context = mp.get_context("fork")
        self.connection, child = context.Pipe()
        self.process = context.Process(target=_serve, args=(child, operations), daemon=True)
        self.process.start()
        child.close()

    def call(self, operation, argument, timeout):
        if timeout <= 0:
            raise WorkerTimeout()
        try:
            self.connection.send((operation, argument))
            if not self.connection.poll(timeout):
                raise WorkerTimeout()
            success, value = self.connection.recv()
        except (EOFError, BrokenPipeError, OSError) as exc:
            raise WorkerError("Noisy worker exited") from exc
        if not success:
            raise WorkerError(value)
        return value

    def close(self):
        self.connection.close()
        if self.process.is_alive():
            self.process.terminate()
        self.process.join(timeout=0.05)
        if self.process.is_alive():
            self.process.kill()
            self.process.join(timeout=0.05)
