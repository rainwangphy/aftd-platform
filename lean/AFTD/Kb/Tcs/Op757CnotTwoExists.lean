import AFTD.Prelude
import AFTD.Kb.Tcs.TwoSidedShadowOptimalScore
import AFTD.Kb.Tcs.CliffordGate
import AFTD.Kb.Tcs.CliffordCnotCount
import AFTD.Kb.Tcs.Is1dChainCircuit
import AFTD.Kb.Tcs.CliffordCircuitScore

/-!
# op_757_cnot_two_exists

Topic: quantum   Node: 710bcd7bafc2

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:1658

For k = 2, there exists a Clifford circuit circ : List (CliffordGate 2) satisfying is_1d_chain_circuit circ and clifford_circuit_score circ = two_sided_shadow_optimal_score 2 with clifford_cnot_count circ <= 2.
-/

/-- Partial result for OP-757: 2 CNOTs suffice on 2 qubits. -/
theorem op_757_cnot_two_exists :
    ∃ circ : List (CliffordGate 2),
      is_1d_chain_circuit circ ∧
      clifford_circuit_score circ = two_sided_shadow_optimal_score 2 ∧
      clifford_cnot_count circ ≤ 2 := ⟨[CliffordGate.cnot 0 1 (by decide)], rfl, by decide, by decide⟩
