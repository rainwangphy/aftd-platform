import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxExistsOfPositivePerturbations
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods

/-!
# efx_exists_of_strictly_positive_profiles

Topic: fair_division   Node: 0b51764fb8a8

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01.

For fixed finite numbers of goods and agents, existence of complete EFX for every strictly positive real additive profile implies complete EFX existence for every nonnegative real additive profile.
-/

open Function Finset

theorem efx_exists_of_strictly_positive_profiles (m n : ℕ)
    (h : ∀ v : Fin n → Fin m → ℝ, (∀ i g, 0 < v i g) →
      ∃ σ : Fin m → Fin n, is_efx_goods v σ)
    (u : Fin n → Fin m → ℝ) (hu : ∀ i g, 0 ≤ u i g) :
    ∃ σ : Fin m → Fin n, is_efx_goods u σ := by
  apply efx_exists_of_positive_perturbations u
  intro ε hε
  exact h (fun i g => u i g + ε) (fun i g => add_pos_of_nonneg_of_pos (hu i g) hε)
