import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuationEraseOfMem
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_efx_goods_iff_bundle_totals

Topic: fair_division   Node: 0a0d2f8f6d3b

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01.

For real additive valuations, EFX is equivalent to the following total-value inequalities: for every pair of distinct agents i,j and each good g assigned to j, the total value of j's bundle to i is at most i's own total plus i's value of g.
-/

open Function Finset

theorem is_efx_goods_iff_bundle_totals {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) :
    is_efx_goods u σ ↔ ∀ i j : Fin n, i ≠ j → ∀ g : Fin m, σ g = j →
      additive_valuation (u i) (bundle_of σ j) ≤
        additive_valuation (u i) (bundle_of σ i) + u i g := by
  constructor
  · intro h i j hij g hg
    have hmem : g ∈ bundle_of σ j := by simpa [bundle_of] using hg
    have hh := h i j hij g hmem
    rw [additive_valuation_erase_of_mem _ _ _ hmem] at hh
    exact sub_le_iff_le_add.mp hh
  · intro h i j hij g hg
    have heq : σ g = j := by simpa [bundle_of] using hg
    rw [additive_valuation_erase_of_mem _ _ _ hg]
    exact sub_le_iff_le_add.mpr (h i j hij g heq)
