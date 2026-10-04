import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb
import AFTD.Kb.GameTheoryEconomics.SpiIsScheme
import AFTD.Kb.GameTheoryEconomics.SpiAcceptReduction

/-!
# spi_accept_prob_mem_Icc

Topic: mechanism_design   Node: d0f76e359b8f

Acceptance probabilities of valid schemes on two-point rewards lie in [0, 1].
-/

open Finset in
/-- Acceptance probabilities are probabilities: for a scheme and probability weights, `0 ≤ P_i ≤ 1` (stated for two-point rewards). -/
lemma spi_accept_prob_mem_Icc {N S : ℕ} (x w : Fin N → Fin 2 → ℝ) (φ : Fin N → Fin 2 → Fin S → ℝ)
    (T : ℝ) (i : Fin N) (hw : ∀ k, 0 ≤ w i k) (hsum : w i 0 + w i 1 = 1) (hφ : spi_is_scheme (φ i)) :
    0 ≤ spi_accept_prob x w φ T i ∧ spi_accept_prob x w φ T i ≤ 1 := by
  obtain ⟨A, hA, hP, -, -⟩ := spi_accept_reduction x w φ T i hw hφ
  rw [hP, Fin.sum_univ_two]
  constructor <;> linarith [hA 0, hA 1]
