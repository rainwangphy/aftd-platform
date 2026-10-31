import AFTD.Prelude
import AFTD.Kb.Tcs.TwoSidedShadowOptimalScore
import AFTD.Kb.Tcs.CliffordGate
import AFTD.Kb.Tcs.CliffordCnotCount
import AFTD.Kb.Tcs.Is1dChainCircuit
import AFTD.Kb.Tcs.CliffordCircuitScore

/-!
# op_757_1d_chain_cnot_three_le_five

Topic: quantum   Node: ed8f4a7a0a64

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:1669

For k = 3 with 1D nearest-neighbor chain connectivity, there exists a Clifford circuit circ : List (CliffordGate 3) satisfying is_1d_chain_circuit circ and clifford_circuit_score circ = two_sided_shadow_optimal_score 3 with clifford_cnot_count circ <= 5.
-/

/-- Partial result for OP-757: 5 CNOTs suffice on a 1D chain for k = 3, beating the dual-axis bound of 6. -/
theorem op_757_1d_chain_cnot_three_le_five :
    ∃ circ : List (CliffordGate 3),
      is_1d_chain_circuit circ ∧
      clifford_circuit_score circ = two_sided_shadow_optimal_score 3 ∧
      clifford_cnot_count circ ≤ 5 := by
  refine ⟨[CliffordGate.s 1, CliffordGate.s 0, CliffordGate.h 2,
   CliffordGate.cnot 1 0 (by decide),
   CliffordGate.s 1, CliffordGate.h 1,
   CliffordGate.cnot 1 2 (by decide),
   CliffordGate.s 2, CliffordGate.h 2,
   CliffordGate.cnot 0 1 (by decide),
   CliffordGate.h 2,
   CliffordGate.cnot 1 2 (by decide),
   CliffordGate.s 2, CliffordGate.h 0, CliffordGate.h 2,
   CliffordGate.cnot 0 1 (by decide),
   CliffordGate.h 1, CliffordGate.s 1, CliffordGate.s 1], ?_, ?_, ?_⟩
  · unfold is_1d_chain_circuit
    decide
  · decide
  · decide
