import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimal
import AFTD.Kb.GameTheoryEconomics.GoodsUtility
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_fractionally_pareto_optimal_zero_goods

Topic: fair_division   Node: 9ec2810545d7

Provenance: helper lemma. folklore

When there are no goods, every complete allocation is fractionally Pareto optimal.
-/

/-- Vacuous fractional Pareto optimality when there are no goods. -/
theorem is_fractionally_pareto_optimal_zero_goods (n : ℕ) (u : Fin n → Fin 0 → ℝ) (σ : Fin 0 → Fin n) :
    is_fractionally_pareto_optimal u σ := by
  intro ⟨x, _, _, _, ⟨i, h_lt⟩⟩
  simp [goods_utility, additive_valuation, bundle_of] at h_lt
