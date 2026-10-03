import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_weighted_propx_chores

Topic: fair_division   Node: 60f149ed0050

Weighted PROPX for chores (zero-tolerant): for every agent i and every chore e in her bundle, her cost for the bundle without e is at most s_i times her cost for all chores.
-/

/-- Weighted PROPX for chores (arXiv:2608.16130, Def. 2.3, zero-tolerant version): for every agent `i` and every chore `e` in her bundle, her cost for the bundle without `e` is at most `s i * c i (M)`. Costs are additive (`additive_valuation`), `M = Finset.univ`. -/
def is_weighted_propx_chores {m n : ℕ} (c : Fin n → Fin m → ℝ) (s : Fin n → ℝ)
    (σ : Fin m → Fin n) : Prop :=
  ∀ i, ∀ e ∈ bundle_of σ i,
    additive_valuation (c i) (bundle_of σ i \ {e}) ≤ s i * additive_valuation (c i) Finset.univ
