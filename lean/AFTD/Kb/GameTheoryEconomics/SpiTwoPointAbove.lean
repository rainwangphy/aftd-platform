import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb
import AFTD.Kb.GameTheoryEconomics.SpiAcceptValue
import AFTD.Kb.GameTheoryEconomics.SpiIsScheme
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxValue
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProbMemIcc
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointBound
import AFTD.Kb.GameTheoryEconomics.SpiIsTwoPointInstance

/-!
# spi_two_point_above

Topic: mechanism_design   Node: 1612323c2ca6

Above its high value (T > h) a two-point player is never accepted, whatever its scheme.
-/

/-- Above the high value (`T > h`) a two-point player is never accepted, whatever its scheme. -/
lemma spi_two_point_above {N S : ℕ} (x w : Fin N → Fin 2 → ℝ) (hinst : spi_is_two_point_instance x w)
    (T : ℝ) (φ : Fin N → Fin 2 → Fin S → ℝ) {i : Fin N} (hφ : spi_is_scheme (φ i)) (hT : x i 0 < T) :
    spi_accept_prob x w φ T i = 0 ∧ spi_accept_value x w φ T i = 0 := by
  obtain ⟨-, hlh, h0, h1, hw1⟩ := hinst i
  have hb := spi_two_point_bound x w φ T i hlh h0 h1 hw1 hφ
  have hw : ∀ k, 0 ≤ w i k := by
    intro k; fin_cases k
    · exact h0
    · simp only [Fin.mk_one, hw1]; linarith
  have hP := (spi_accept_prob_mem_Icc x w φ T i hw (by rw [hw1]; ring) hφ).1
  have hm : spi_two_point_max_prob (x i 0) (x i 1) (w i 0) T = 0 := by
    unfold spi_two_point_max_prob
    rw [if_neg (by nlinarith), if_neg (by linarith)]
  have hv : spi_two_point_max_value (x i 0) (x i 1) (w i 0) T = 0 := by
    unfold spi_two_point_max_value
    rw [if_neg (by nlinarith), if_neg (by linarith)]
  rw [hm] at hb
  have hP0 : spi_accept_prob x w φ T i = 0 := le_antisymm hb.1 hP
  exact ⟨hP0, by rw [hb.2 hP0.ge, hv]⟩
