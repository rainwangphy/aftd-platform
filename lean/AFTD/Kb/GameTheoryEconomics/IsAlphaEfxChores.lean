import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_alpha_efx_chores

Topic: fair_division   Node: b3111ab99f1d

Provenance: formalization of a published result. Source: scout/2611-00432-online-fair-division-of-chores-with-upgrade-recourse.md:261

An allocation σ of m chores among n agents is α-EFX under additive costs c if for every pair of distinct agents i and j, and every chore e in i's bundle bundle_of σ i, agent i's cost for bundle_of σ i minus e (additive_valuation (c i) (bundle_of σ i) - c i e) is at most α times agent i's cost for j's bundle (additive_valuation (c i) (bundle_of σ j)).
-/

/-- An allocation of m chores to n agents is α-EFX under additive costs c if for every pair of distinct agents i and j, and every chore e assigned to i, agent i's cost for her bundle without e is at most α times her cost for j's bundle. -/
def is_alpha_efx_chores {m n : ℕ} (α : ℝ) (c : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop := ∀ (i j : Fin n), i ≠ j → ∀ e ∈ bundle_of σ i,
  additive_valuation (c i) (bundle_of σ i) - c i e ≤ α * additive_valuation (c i) (bundle_of σ j)
