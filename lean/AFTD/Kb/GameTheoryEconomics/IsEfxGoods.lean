import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_efx_goods

Topic: fair_division   Node: 1e6cea3a12d1

Provenance: formalization of a published result. Source: arXiv:2610.29201 Def 1

An allocation is EFX if for every pair of distinct agents i and j, and every good g in j's bundle, agent i values her own bundle at least as much as j's bundle without g.
-/

/-- An allocation of goods is EFX if removing any good from another agent's bundle eliminates envy. -/
def is_efx_goods {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ g ∈ bundle_of σ j,
    additive_valuation (u i) ((bundle_of σ j).erase g) ≤ additive_valuation (u i) (bundle_of σ i)
