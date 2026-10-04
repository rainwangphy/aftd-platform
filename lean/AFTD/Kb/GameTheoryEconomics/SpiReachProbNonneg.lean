import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiReachProb
import AFTD.Kb.GameTheoryEconomics.SpiIsScheme
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProbMemIcc
import AFTD.Kb.GameTheoryEconomics.SpiIsTwoPointInstance

/-!
# spi_reach_prob_nonneg

Topic: mechanism_design   Node: 8611bdf75fec

Reach probabilities are nonnegative in a two-point instance under valid schemes.
-/

open Finset in
/-- Reach probabilities are nonnegative in a two-point instance under valid schemes. -/
lemma spi_reach_prob_nonneg {N S : ℕ} (x w : Fin N → Fin 2 → ℝ) (hinst : spi_is_two_point_instance x w)
    (φ : Fin N → Fin 2 → Fin S → ℝ) (hφ : ∀ i, spi_is_scheme (φ i)) (T : ℝ) (i : Fin N) :
    0 ≤ spi_reach_prob x w φ T i := by
  unfold spi_reach_prob
  refine Finset.prod_nonneg fun j _ => ?_
  obtain ⟨-, -, h0, h1, hw1⟩ := hinst j
  have hw : ∀ k, 0 ≤ w j k := by
    intro k; fin_cases k
    · exact h0
    · simp only [Fin.mk_one, hw1]; linarith
  have := spi_accept_prob_mem_Icc x w φ T j hw (by rw [hw1]; ring) (hφ j)
  linarith [this.2]
