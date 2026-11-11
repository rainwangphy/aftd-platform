import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinExpectedManipulationGain
import AFTD.Kb.GameTheoryEconomics.RoundRobinBordaGainTwoGoods
import AFTD.Kb.GameTheoryEconomics.RoundRobinUBest
import AFTD.Kb.GameTheoryEconomics.RoundRobinBordaManipulationGain
import AFTD.Kb.GameTheoryEconomics.RoundRobinUTruth

/-!
# round_robin_expected_manipulation_gain_two_eq_zero

Topic: fair_division   Node: e8610e62ea05

Provenance: helper lemma. OP-1439

For m = 2 goods, the expected real-valued normalized strategic manipulation gain round_robin_expected_manipulation_gain 2 equals 0.
-/

/-- The expected normalized manipulation gain is zero for m = 2 goods. -/
theorem round_robin_expected_manipulation_gain_two_eq_zero :
    round_robin_expected_manipulation_gain 2 = 0 := by
  unfold round_robin_expected_manipulation_gain
  have h : ∀ p : (Fin 2 ≃ Fin 2) × (Fin 2 ≃ Fin 2),
      round_robin_borda_manipulation_gain 2 p.1 p.2 = 0 := by
    rintro ⟨rA, rB⟩
    unfold round_robin_borda_manipulation_gain
    rw [round_robin_borda_gain_two_goods rA rB]
    simp
  simp [h]
