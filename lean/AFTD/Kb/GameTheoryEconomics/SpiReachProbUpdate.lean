import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiReachProb
import AFTD.Kb.GameTheoryEconomics.SpiAcceptCongr

/-!
# spi_reach_prob_update

Topic: mechanism_design   Node: 98dd1dce7ae0

A unilateral deviation of player i does not change the probability that the search reaches i.
-/

open Finset in
/-- A unilateral deviation of player `i` does not change the probability that the search reaches `i`. -/
lemma spi_reach_prob_update {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (φ : Fin N → Fin K → Fin S → ℝ)
    (T : ℝ) (i : Fin N) (ψ : Fin K → Fin S → ℝ) :
    spi_reach_prob x w (Function.update φ i ψ) T i = spi_reach_prob x w φ T i := by
  unfold spi_reach_prob
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := ne_of_lt (Finset.mem_filter.mp hj).2
  rw [(spi_accept_congr x w (Function.update φ i ψ) φ T j (Function.update_of_ne hji ψ φ)).1]
