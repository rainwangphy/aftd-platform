import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_alpha_efx_goods

Topic: fair_division   Node: 934a9e79e435

Provenance: formalization of a published result. Source: arXiv:2610.34625, Sec. 4

An allocation of m indivisible goods to n agents is alpha-EFX under additive valuations u if for every pair of distinct agents i and j, and every good g in j's bundle, alpha times i's value for j's bundle without g is at most i's value for i's own bundle.
-/

/-- An allocation of m indivisible goods to n agents is alpha-EFX under additive valuations u if for every pair of distinct agents i and j, and every good g in j's bundle, alpha times i's value for j's bundle without g is at most i's value for i's own bundle. -/
def is_alpha_efx_goods {m n : ℕ} (u : Fin n → Fin m → ℝ) (α : ℝ) (σ : Fin m → Fin n) : Prop := ∀ i j : Fin n, i ≠ j → ∀ g ∈ bundle_of σ j,
    α * additive_valuation (u i) ((bundle_of σ j).erase g) ≤ additive_valuation (u i) (bundle_of σ i)
