"""Export a pinned Python reference model before its solver is constructed.

Authoring only. Requires CPMpy 1.1.0 and minizinc-python 0.10.0; generated Aeon
programs have neither dependency. Each invocation captures the first default
instance with deterministic random seeds and never calls a solver.
"""

import argparse
import contextlib
import hashlib
import io
import json
from pathlib import Path
import random
import sys


class CapturedModel(BaseException):
    def __init__(self, model):
        self.model = model


def capture(source, destination, minizinc_binary, data_scripts=()):
    import cpmpy
    import minizinc
    import numpy as np
    from cpmpy.solvers.minizinc import CPM_minizinc
    from cpmpy.solvers.ortools import CPM_ortools

    if cpmpy.__version__ != "1.1.0" or minizinc.__version__ != "0.10.0":
        raise ValueError("Pinned authoring versions are CPMpy 1.1.0 and minizinc-python 0.10.0")

    def capture_constructor(self, cpm_model=None, subsolver=None):
        if cpm_model is not None:
            raise CapturedModel(cpm_model)
        raise ValueError("Empty native solver construction needs an explicit model")

    original_constructor = CPM_ortools.__init__
    original_arguments = sys.argv
    original_path = list(sys.path)
    original_driver = minizinc.default_driver
    CPM_ortools.__init__ = capture_constructor
    random_state = random.getstate()
    numpy_state = np.random.get_state()
    random.seed(0)
    np.random.seed(0)
    sys.path.insert(0, str(source.parent))
    sys.argv = [str(source), *[str(path) for path in data_scripts]]
    try:
        minizinc.default_driver = minizinc.Driver(minizinc_binary)
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                exec(
                    compile(source.read_text(), str(source), "exec"), {"__name__": "__main__", "__file__": str(source)}
                )
        except CapturedModel as captured:
            exporter = CPM_minizinc(captured.model)
            text = "".join(exporter.mzn_model._code_fragments) + "\n" + exporter.mzn_txt_solve + "\n"
            destination.write_text(text)
            return dict(
                source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                cpmpy_version=cpmpy.__version__,
                minizinc_python_version=minizinc.__version__,
                numpy_version=np.__version__,
                captured_sha256=hashlib.sha256(text.encode()).hexdigest(),
            )
        raise ValueError("No model reached the capture boundary")
    finally:
        CPM_ortools.__init__ = original_constructor
        minizinc.default_driver = original_driver
        random.setstate(random_state)
        np.random.set_state(numpy_state)
        sys.argv = original_arguments
        sys.path[:] = original_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--destination", required=True, type=Path)
    parser.add_argument("--minizinc", required=True, type=Path)
    parser.add_argument("--data-script", action="append", type=Path, default=[])
    args = parser.parse_args()
    print(
        json.dumps(
            capture(
                args.source.resolve(),
                args.destination.resolve(),
                args.minizinc.resolve(),
                [p.resolve() for p in args.data_script],
            )
        )
    )


if __name__ == "__main__":
    main()
