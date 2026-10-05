import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mnw2LbVal
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# mnw2_lb_bundle

Topic: fair_division   Node: 69f248648f16

In the three-good instance, agent i's value for her bundle under σ is the sum of her values of the goods g ∈ {0, 1, 2} with σ(g) = i.
-/

/-- Bundle values in the lower-bound instance, good by good. -/
theorem mnw2_lb_bundle (ε : ℝ) (σ : Fin 3 → Fin 2) (i : Fin 2) : additive_valuation (mnw2_lb_val ε i) (bundle_of σ i) = (if σ 0 = i then mnw2_lb_val ε i 0 else 0) + (if σ 1 = i then mnw2_lb_val ε i 1 else 0) + (if σ 2 = i then mnw2_lb_val ε i 2 else 0) := by
  unfold additive_valuation bundle_of
  rw [Finset.sum_filter, Fin.sum_univ_three]
