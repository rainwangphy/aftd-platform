import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_efx_goods_all_pairs

Topic: fair_division   Node: 6c917c279391

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01.

For nonnegative additive values, the EFX inequalities also hold when the observer and the target agent coincide.
-/

open Function Finset

theorem is_efx_goods_all_pairs {m n : ℕ} (u : Fin n → Fin m → ℝ)
    (hu : ∀ i g, 0 ≤ u i g) (σ : Fin m → Fin n) (hσ : is_efx_goods u σ) :
    ∀ i j : Fin n, ∀ g ∈ bundle_of σ j,
      additive_valuation (u i) ((bundle_of σ j).erase g) ≤
        additive_valuation (u i) (bundle_of σ i) := by
  intro i j g hg
  by_cases hij : i = j
  · subst j
    change (∑ x ∈ (bundle_of σ i).erase g, u i x) ≤ ∑ x ∈ bundle_of σ i, u i x
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset g _)
      (fun x _ _ => hu i x)
  · exact hσ i j hij g hg
