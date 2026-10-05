import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_pmms_fair_chores

Topic: fair_division   Node: cd2e1ba558ce

Pairwise maximin share (PMMS) for chores: allocation σ is PMMS for agent i if, for every other agent j and every way of splitting X_i ∪ X_j into two parts T and (X_i ∪ X_j) \ T, agent i's cost for her own bundle is at most her cost for the more costly of the two parts. Equivalently c_i(X_i) is at most the minimum over two-way splits of the larger part.
-/

/-- Pairwise MMS for chores with additive costs `c`: against every other agent `j`, agent `i`'s cost is at most the larger part of every split of `X_i ∪ X_j` in two, in `i`'s own costs. -/
def is_pmms_fair_chores {m n : ℕ} (c : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → ∀ T ⊆ bundle_of σ i ∪ bundle_of σ j,
    additive_valuation (c i) (bundle_of σ i) ≤
      max (additive_valuation (c i) T)
        (additive_valuation (c i) ((bundle_of σ i ∪ bundle_of σ j) \ T))
