"""Resource measurement helpers used by synthesis fitness functions.

This is the single place where Aeon decides *how* it measures CPU time and
energy for candidate programs evaluated by the synthesizer. Two metrics are
exposed:

- :func:`measure_cputime` — CPU time consumed by a thunk, in seconds.
- :func:`measure_energy`  — energy consumed by a thunk, in joules.

Energy measurement picks the most accurate backend available at runtime and
caches the choice. Backends are tried in order:

1. **Linux powercap** (``/sys/class/powercap/intel-rapl:*/energy_uj``). Works
   for both Intel (``intel_rapl_*`` drivers) and modern AMD CPUs (the
   ``rapl_msr`` / ``amd_energy`` driver, kernel 5.8+) when the relevant
   module is loaded. No third-party dependency required.
2. **CPU-time proxy** (``cpu_time * DEFAULT_POWER_W``). Universal fallback
   used on macOS (Intel and Apple Silicon), Windows, and Linux machines
   without exposed RAPL counters. The proxy is monotonic in CPU time, so
   the search signal is preserved even though absolute joules are not.

To add a new backend, implement :class:`EnergyMeter` and prepend it to
``_BACKENDS`` below.
"""

from __future__ import annotations

import functools
import glob
import time
from typing import Callable, Protocol


# Watts. Used by the CPU-time proxy. The exact value is unimportant; the
# search only needs a monotonic energy estimate, not an absolute one.
DEFAULT_POWER_W = 15.0


Thunk = Callable[[], object]


def measure_cputime(thunk: Thunk) -> float:
    """Run ``thunk`` and return CPU time consumed, in seconds."""
    start = time.process_time()
    thunk()
    return time.process_time() - start


class EnergyMeter(Protocol):
    """Backend that measures the energy consumed running a thunk, in joules."""

    def available(self) -> bool: ...

    def measure(self, thunk: Thunk) -> float: ...


class PowercapMeter:
    """Linux powercap RAPL reader (Intel + AMD).

    Reads ``energy_uj`` (microjoules) for every powercap zone matching
    ``intel-rapl:*`` before and after the thunk and sums the deltas. The
    counters can wrap around at the value advertised in
    ``max_energy_range_uj`` next to each ``energy_uj`` file, but for the
    sub-second evaluations a synthesizer performs that's vanishingly rare;
    we clamp negative deltas to 0 to stay safe.
    """

    PATTERN = "/sys/class/powercap/intel-rapl:*/energy_uj"

    def _files(self) -> list[str]:
        return sorted(glob.glob(self.PATTERN))

    def available(self) -> bool:
        return bool(self._files())

    @staticmethod
    def _read(path: str) -> int:
        with open(path) as f:
            return int(f.read().strip())

    def measure(self, thunk: Thunk) -> float:
        files = self._files()
        before = [self._read(p) for p in files]
        thunk()
        after = [self._read(p) for p in files]
        delta_uj = sum(max(0, a - b) for a, b in zip(after, before))
        return delta_uj / 1e6


class CPUTimeProxyMeter:
    """Universal fallback: ``energy ≈ cpu_time * DEFAULT_POWER_W``."""

    def available(self) -> bool:
        return True

    def measure(self, thunk: Thunk) -> float:
        return measure_cputime(thunk) * DEFAULT_POWER_W


# Ordered from most accurate to least. ``CPUTimeProxyMeter`` is always the
# last entry, so ``default_energy_meter`` is guaranteed to return something.
_BACKENDS: list[EnergyMeter] = [PowercapMeter(), CPUTimeProxyMeter()]


@functools.lru_cache(maxsize=1)
def default_energy_meter() -> EnergyMeter:
    """Return the best energy meter available on this machine (cached)."""
    for m in _BACKENDS:
        if m.available():
            return m
    raise RuntimeError("no energy meter available")  # unreachable


def measure_energy(thunk: Thunk) -> float:
    """Run ``thunk`` and return joules consumed, using the best backend."""
    return default_energy_meter().measure(thunk)
