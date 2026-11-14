import AFTD.Prelude
import AFTD.Kb.Tcs.ClosedNetworkEndNodeResponseBound

/-!
# three_qubit_dof_inequality

Topic: quantum   Node: 350591762cec

Provenance: formalization of a published result. Source: arXiv:2611.16921 Sec. II.2 -- When can local unitaries generate a complete orthogonal basis?

For three qubits (d₁ = d₂ = d₃ = 2), the dimensional degree-of-freedom inequality ∑_{j=1}^3 d_j^2 ≥ ∏_{j=1}^3 d_j + 3 holds, that is, 2^2 + 2^2 + 2^2 ≥ 2^3 + 3 (12 ≥ 11).
-/

/-- The dimensional degree-of-freedom heuristic inequality holds for three qubits: 2^2 + 2^2 + 2^2 ≥ 2^3 + 3. -/
theorem three_qubit_dof_inequality : (2 : ℕ)^2 + 2^2 + 2^2 ≥ 2^3 + 3 := by first | exact closed_network_end_node_response_bound | (apply closed_network_end_node_response_bound <;> assumption) | (apply closed_network_end_node_response_bound <;> simp_all) | simpa using closed_network_end_node_response_bound
