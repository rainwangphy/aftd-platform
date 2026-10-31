import AFTD.Prelude
import AFTD.Kb.Tcs.TwoSidedShadowOptimalScore
import AFTD.Kb.Tcs.CliffordGate
import AFTD.Kb.Tcs.CliffordCnotCount
import AFTD.Kb.Tcs.CliffordCircuitScore

/-!
# op_757_all_to_all_cnot_three_exists

Topic: quantum   Node: 8aa95403f86d

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:1658

For k = 3 with all-to-all connectivity, there exists a Clifford circuit circ : List (CliffordGate 3) achieving clifford_circuit_score circ = two_sided_shadow_optimal_score 3 with clifford_cnot_count circ = 4.
-/

/-- Partial result for OP-757: exact CNOT count 4 on 3 qubits with all-to-all connectivity. -/
theorem op_757_all_to_all_cnot_three_exists :
    ∃ circ : List (CliffordGate 3),
      clifford_circuit_score circ = two_sided_shadow_optimal_score 3 ∧
      clifford_cnot_count circ = 4 := by
  refine ⟨[CliffordGate.cnot 2 0 (by decide), CliffordGate.h 2,
      CliffordGate.cnot 0 1 (by decide), CliffordGate.s 0, CliffordGate.s 2,
      CliffordGate.cnot 1 2 (by decide), CliffordGate.cnot 2 0 (by decide)], ?_, ?_⟩
  · decide
  · decide
