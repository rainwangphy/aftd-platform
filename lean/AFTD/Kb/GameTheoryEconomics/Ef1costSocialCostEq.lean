import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.SocialCost

/-!
# ef1cost_social_cost_eq

Topic: fair_division   Node: a9cab9e1af64

The social cost of an allocation equals the sum over items of the cost of each item to its owner.
-/

lemma ef1cost_social_cost_eq {m n : ℕ} (c : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) :
    social_cost c σ = ∑ j, c (σ j) j := by
  classical
  simp only [social_cost, additive_valuation, bundle_of, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp
