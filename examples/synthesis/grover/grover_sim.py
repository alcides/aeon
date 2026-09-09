"""Native helpers for the Aeon HUMIES-2026 Grover-circuit benchmark.

Noiseless 3-qubit statevector simulation and the scalar fitness of

    Obidiegwu, Mota Dias, Obidiegwu & Ryan, "Evolving Hardware-Efficient
    Grover Circuits with Grammatical Evolution", GECCO 2026
    (2026 HUMIES Bronze; reference code: github.com/Caephas/GE-for-Grover).

The paper evolves state-specific 3-qubit Grover-like circuits with GE and
scores them (tournament mode, run_experiment.py of the reference code) by the
minimised scalar

    fitness = 10 * miss + (1 - P_target) + GATE_PENALTY_WEIGHT * gate_count
    miss    = 1 if P_target < SUCCESS_THRESHOLD (0.48) else 0

where P_target is the probability of measuring the target basis state. As in
the paper's grammar, every circuit starts from |000> with a fixed Hadamard
layer on all three qubits (Grover's uniform-superposition setup); only the
gates after that layer are evolved. Here P_target is the *exact* statevector
probability (the paper samples 10k shots on Qiskit's noiseless AerSimulator,
which converges to the same value), so no Qiskit dependency is needed: a
3-qubit state is just 8 complex amplitudes, simulated in pure Python.

A Circuit value arrives from Aeon as nested tuples (one per gate, ending in
the terminator), e.g. H(0); CX(0,1) is

    ('Circuit_g_h', 0, ('Circuit_g_cx', 0, 1, ('Circuit_g_end',)))

Qubit/bit convention (Qiskit little-endian): bit q of a basis-state index is
qubit q, so target 6 = 0b110 means qubit 2 = 1, qubit 1 = 1, qubit 0 = 0.
"""

import cmath
import math

N_QUBITS = 3
DIM = 1 << N_QUBITS

SUCCESS_THRESHOLD = 0.48  # paper: miss if P_target below this
GATE_PENALTY_WEIGHT = 0.02  # paper: lambda, per-gate parsimony pressure

# A synthesised gate sequence can be arbitrarily long; evaluation is linear in
# its length, so a generous cap keeps a single fitness call bounded without
# affecting realistic candidates (the paper's circuits are tens of gates).
MAX_GATES = 1024

_H = 1 / math.sqrt(2)
_SINGLE_QUBIT_GATES = {
    "x": ((0, 1), (1, 0)),
    "y": ((0, -1j), (1j, 0)),
    "z": ((1, 0), (0, -1)),
    "h": ((_H, _H), (_H, -_H)),
    "s": ((1, 0), (0, 1j)),
    "sdg": ((1, 0), (0, -1j)),
    "t": ((1, 0), (0, cmath.exp(1j * math.pi / 4))),
    "tdg": ((1, 0), (0, cmath.exp(-1j * math.pi / 4))),
}


def _apply_single(state, q, m):
    """Apply a 2x2 unitary m to qubit q of the 8-amplitude state, in place."""
    bit = 1 << q
    for i in range(DIM):
        if not i & bit:
            a0, a1 = state[i], state[i | bit]
            state[i] = m[0][0] * a0 + m[0][1] * a1
            state[i | bit] = m[1][0] * a0 + m[1][1] * a1


def _gate_list(circuit):
    """Flatten the Aeon Circuit tuple chain into [(gate_name, args)]."""
    gates = []
    node = circuit
    while node[0] != "Circuit_g_end" and len(gates) < MAX_GATES:
        gates.append((node[0].removeprefix("Circuit_g_"), node[1:-1]))
        node = node[-1]
    return gates


def simulate(circuit):
    """Run the fixed Hadamard layer + evolved gates; return (state, gate_count).

    gate_count includes the 3 fixed initial Hadamards, matching the paper's
    whole-circuit gate count. A two-qubit gate whose control and target
    coincide is a no-op but still counts, so parsimony pressure steers the
    search away from degenerate gates.
    """
    state = [0j] * DIM
    state[0] = 1 + 0j
    for q in range(N_QUBITS):
        _apply_single(state, q, _SINGLE_QUBIT_GATES["h"])

    gates = _gate_list(circuit)
    for name, args in gates:
        if name in _SINGLE_QUBIT_GATES:
            _apply_single(state, args[0], _SINGLE_QUBIT_GATES[name])
        elif name == "cx":
            c, t = args
            if c != t:
                cbit, tbit = 1 << c, 1 << t
                for i in range(DIM):
                    if i & cbit and not i & tbit:
                        state[i], state[i | tbit] = state[i | tbit], state[i]
        elif name == "cz":
            c, t = args
            if c != t:
                both = (1 << c) | (1 << t)
                for i in range(DIM):
                    if i & both == both:
                        state[i] = -state[i]
        elif name == "ccx":
            # On 3 qubits the two controls are simply the non-target qubits.
            (t,) = args
            tbit = 1 << t
            controls = (DIM - 1) & ~tbit
            for i in range(DIM):
                if i & controls == controls and not i & tbit:
                    state[i], state[i | tbit] = state[i | tbit], state[i]
        else:
            raise ValueError(f"unknown gate constructor: {name}")
    return state, N_QUBITS + len(gates)


def p_target(circuit, target):
    """Exact probability of measuring basis state `target` (0..7)."""
    state, _ = simulate(circuit)
    return abs(state[target]) ** 2


def fitness(circuit, target):
    """The paper's minimised scalar fitness (0.12 is optimal for target 0)."""
    state, gate_count = simulate(circuit)
    p = abs(state[target]) ** 2
    miss = 1 if p < SUCCESS_THRESHOLD else 0
    return 10 * miss + (1 - p) + GATE_PENALTY_WEIGHT * gate_count
