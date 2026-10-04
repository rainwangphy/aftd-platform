import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb
import AFTD.Kb.GameTheoryEconomics.SpiReachProb

/-!
# spi_reach_prob_fin_four

Topic: mechanism_design   Node: 4adbe4c0dc25

For four players the reach probabilities are 1, 1-P0, (1-P0)(1-P1) and (1-P0)(1-P1)(1-P2).
-/

open Finset in
/-- For four players, the reach probabilities are `1`, `1 - P₀`, `(1 - P₀)(1 - P₁)` and `(1 - P₀)(1 - P₁)(1 - P₂)`. -/
lemma spi_reach_prob_fin_four {K S : ℕ} (x w : Fin 4 → Fin K → ℝ) (φ : Fin 4 → Fin K → Fin S → ℝ) (T : ℝ) :
    spi_reach_prob x w φ T 0 = 1 ∧
    spi_reach_prob x w φ T 1 = 1 - spi_accept_prob x w φ T 0 ∧
    spi_reach_prob x w φ T 2 = (1 - spi_accept_prob x w φ T 0) * (1 - spi_accept_prob x w φ T 1) ∧
    spi_reach_prob x w φ T 3 = (1 - spi_accept_prob x w φ T 0) * (1 - spi_accept_prob x w φ T 1) *
      (1 - spi_accept_prob x w φ T 2) := by
  simp [spi_reach_prob, Finset.prod_filter, Fin.prod_univ_four]
