"""BNSynth's architecture-1 gated CNF network (optional CPU PyTorch).

Product t-norm and its dual t-conorm, as in sections 2.4/3.3 of
https://arxiv.org/abs/2212.08170. Each output learns its own network.
No SAT-generated gates or truth-table-to-CNF fallback is used.
"""

import torch


class GatedCNF(torch.nn.Module):
    def __init__(self, inputs: int, bound: int, generator: torch.Generator):
        super().__init__()
        self.inputs = inputs
        self.bound = bound
        self.literal_gates = torch.nn.Parameter(
            torch.rand((bound, 2 * inputs), generator=generator, dtype=torch.float64)
        )
        self.clause_gates = torch.nn.Parameter(torch.rand((bound,), generator=generator, dtype=torch.float64))

    def forward(self, inputs):
        literals = torch.cat((inputs, 1 - inputs), dim=1)
        clauses = 1 - (1 - literals[:, None, :] * self.literal_gates).prod(dim=2)
        return (1 - self.clause_gates * (1 - clauses)).prod(dim=1)

    def project(self):
        with torch.no_grad():
            self.literal_gates.clamp_(0, 1)
            self.clause_gates.clamp_(0, 1)

    def regularization(self):
        # Matches the reference architecture-1 regression objective.
        return 1e-6 * (self.literal_gates.sum() + (1 - self.clause_gates).sum())

    def clauses(self) -> tuple[tuple[int, ...], ...]:
        """Threshold the gates; remove tautologies/duplicates, never add clauses."""
        literals = (self.literal_gates.detach() > 0.5).tolist()
        active = (self.clause_gates.detach() > 0.5).tolist()
        result = set()
        for enabled, row in zip(active, literals):
            if not enabled:
                continue
            clause = tuple(i + 1 for i, flag in enumerate(row[: self.inputs]) if flag) + tuple(
                -(i + 1) for i, flag in enumerate(row[self.inputs :]) if flag
            )
            if any(-v in clause for v in clause):
                continue
            if not clause:
                return ((),)
            result.add(tuple(sorted(clause)))
        return tuple(sorted(result))

    def fits(self, inputs, targets) -> bool:
        with torch.no_grad():
            predicted = torch.ones(len(inputs), dtype=torch.bool)
            for clause in self.clauses():
                satisfied = torch.zeros(len(inputs), dtype=torch.bool)
                for literal in clause:
                    values = inputs[:, abs(literal) - 1].bool()
                    satisfied |= values if literal > 0 else ~values
                predicted &= satisfied
            return bool(torch.equal(predicted, targets.bool()))
