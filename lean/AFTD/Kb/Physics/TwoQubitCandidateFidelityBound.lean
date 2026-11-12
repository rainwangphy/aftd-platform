import AFTD.Prelude
import AFTD.Kb.Physics.BinaryEntropyNats

/-!
# two_qubit_candidate_fidelity_bound

Topic: quantum_mechanics   Node: 5b53042e0bb1

Provenance: formalization of a published result. Source: OP-1552; arXiv:2409.01966

For ε ≥ 0, two_qubit_candidate_fidelity_bound ε is the infimum over 0 ≤ p, q ≤ 1 of max{ p(1 + 2 sqrt(q(1 - q)))/2, (1 - p)/2 } subject to ln 2 + h(p) - h(pq) ≤ ε, where h is binary entropy in nats.
-/

/-- Candidate minimum fully entangled fraction over the two-parameter family subject to adjusted entropy deficit at most epsilon. -/
noncomputable def two_qubit_candidate_fidelity_bound (ε : ℝ) : ℝ := sInf { F : ℝ | ∃ p q : ℝ,
    0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1 ∧
    Real.log 2 + binary_entropy_nats p - binary_entropy_nats (p * q) ≤ ε ∧
    F = max (p * (1 + 2 * Real.sqrt (q * (1 - q))) / 2) ((1 - p) / 2) }
