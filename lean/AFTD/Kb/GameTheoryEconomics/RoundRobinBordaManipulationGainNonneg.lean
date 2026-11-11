import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinBordaManipulationGain
import AFTD.Kb.GameTheoryEconomics.RoundRobinUBest
import AFTD.Kb.GameTheoryEconomics.RoundRobinUTruth
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.BordaBundleUtility
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome

/-!
# round_robin_borda_manipulation_gain_nonneg

Topic: fair_division   Node: 632cc7c7489a

Provenance: helper lemma. Algorithms for Manipulating Sequential Allocation (AAAI 2020)

For every number of goods m and all rankings rA and rB, the real-valued normalized manipulation gain round_robin_borda_manipulation_gain m rA rB is non-negative (at least 0).
-/

/-- The normalized strategic manipulation gain is always non-negative. -/
theorem round_robin_borda_manipulation_gain_nonneg (m : ℕ) (rA rB : Fin m ≃ Fin m) :
    0 ≤ round_robin_borda_manipulation_gain m rA rB := by
  unfold round_robin_borda_manipulation_gain
  have h_le : round_robin_u_truth m rA rB ≤ round_robin_u_best m rA rB :=
    Finset.le_sup (s := Finset.univ) (b := rA) (f := fun rA' => borda_bundle_utility m rA
      (picking_sequence_outcome (round_robin_sequence 2 m) (fun i => if i = 0 then rA' else rB) 0))
      (Finset.mem_univ rA)
  have h_sub : 0 ≤ (round_robin_u_best m rA rB : ℝ) - (round_robin_u_truth m rA rB : ℝ) := by
    rw [sub_nonneg]
    exact Nat.cast_le.mpr h_le
  exact div_nonneg h_sub (sq_nonneg (m : ℝ))
