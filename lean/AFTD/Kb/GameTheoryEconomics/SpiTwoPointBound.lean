import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb
import AFTD.Kb.GameTheoryEconomics.SpiAcceptValue
import AFTD.Kb.GameTheoryEconomics.SpiIsScheme
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxProb
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointMaxValue
import AFTD.Kb.GameTheoryEconomics.SpiAcceptReduction
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointCore

/-!
# spi_two_point_bound

Topic: mechanism_design   Node: 5e61c8e048db

Provenance: formalization of a published result. Source: Intrinsic Robustness of Prophet Inequality to Strategic Reward Signaling, NeurIPS 2024 (arXiv:2409.18269), Proposition 3.1 (optimal information revealing strategy under threshold T); special case of two-point rewards, finite signal sets

For a two-point reward, every scheme's acceptance probability is at most spi_two_point_max_prob, and if it attains it the accepted value equals spi_two_point_max_value.
-/

open Finset in
/-- For a two-point reward (`x i 0 = h ≥ x i 1 = l`, `w i 0 = q`, `w i 1 = 1 - q`), every scheme's acceptance probability is at most `spi_two_point_max_prob`, and if it attains it the accepted value equals `spi_two_point_max_value`. -/
lemma spi_two_point_bound {N S : ℕ} (x w : Fin N → Fin 2 → ℝ) (φ : Fin N → Fin 2 → Fin S → ℝ)
    (T : ℝ) (i : Fin N) (hlh : x i 1 ≤ x i 0) (hq0 : 0 ≤ w i 0) (hq1 : w i 0 ≤ 1)
    (hw1 : w i 1 = 1 - w i 0) (hφ : spi_is_scheme (φ i)) :
    spi_accept_prob x w φ T i ≤ spi_two_point_max_prob (x i 0) (x i 1) (w i 0) T ∧
      (spi_two_point_max_prob (x i 0) (x i 1) (w i 0) T ≤ spi_accept_prob x w φ T i →
        spi_accept_value x w φ T i = spi_two_point_max_value (x i 0) (x i 1) (w i 0) T) := by
  have hw : ∀ k, 0 ≤ w i k := by
    intro k; fin_cases k
    · exact hq0
    · simp only [Fin.mk_one, hw1]; linarith
  obtain ⟨A, hA, hP, hV, hc⟩ := spi_accept_reduction x w φ T i hw hφ
  simp only [Fin.sum_univ_two] at hP hV hc
  have hA1 := hA 1
  rw [hw1] at hA1
  have core := spi_two_point_core (x i 0) (x i 1) (w i 0) T (A 0) (A 1) hlh hq0 hq1 (hA 0).1 (hA 0).2
    hA1.1 hA1.2 hc
  rw [hP, hV]
  exact core
