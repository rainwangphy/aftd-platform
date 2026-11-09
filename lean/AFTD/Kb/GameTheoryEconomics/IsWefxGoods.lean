import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_wefx_goods

Topic: fair_division   Node: 794141fd86bf

Provenance: formalization of a published result. Source: arXiv:2305.16081, Def. 3

An allocation σ of m goods to n agents with positive entitlements w is weighted EFX (WEFX) if for every pair of distinct agents i and j, and every good g in j's bundle, agent i's additive value for j's bundle without g divided by j's entitlement w_j is at most agent i's value for her own bundle divided by i's entitlement w_i.
-/

/-- Weighted EFX (WEFX): for all distinct agents i and j and every good g in j's bundle, v_i(A_j \ {g}) / w_j ≤ v_i(A_i) / w_i. -/
def is_wefx_goods {m n : ℕ} (w : Fin n → ℝ) (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ g ∈ bundle_of σ j,
    additive_valuation (u i) ((bundle_of σ j).erase g) / w j ≤ additive_valuation (u i) (bundle_of σ i) / w i
