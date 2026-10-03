import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_ef1_goods

Topic: fair_division   Node: d83be5a6fe46

EF1 for goods: every agent i either does not envy agent j, or stops envying j after some single good is removed from j's bundle.
-/

/-- EF1 for goods (Caragiannis et al., The Unreasonable Fairness of Maximum Nash Welfare, Def. 2.2 with footnote 1): for all agents `i, j`, either `i` does not envy `j`, or removing some good from `j`'s bundle removes the envy. -/
def is_ef1_goods {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ i j, additive_valuation (u i) (bundle_of σ j) ≤ additive_valuation (u i) (bundle_of σ i) ∨
    ∃ g ∈ bundle_of σ j, additive_valuation (u i) ((bundle_of σ j).erase g) ≤
      additive_valuation (u i) (bundle_of σ i)
