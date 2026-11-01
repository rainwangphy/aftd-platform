import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuationBundleSumIte
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsIffBundleTotals
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_efx_goods_equiv_goods

Topic: fair_division   Node: 7194caf1ab4f

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01.

Relabeling a finite set of goods through a bijection, both in the valuation profile and allocation, preserves and reflects EFX.
-/

open Function Finset

theorem is_efx_goods_equiv_goods {m k n : ℕ} (e : Fin m ≃ Fin k)
    (u : Fin n → Fin k → ℝ) (σ : Fin k → Fin n) :
    is_efx_goods (fun i g => u i (e g)) (fun g => σ (e g)) ↔ is_efx_goods u σ := by
  have hval (i j : Fin n) :
      additive_valuation (fun g => u i (e g)) (bundle_of (fun g => σ (e g)) j) =
        additive_valuation (u i) (bundle_of σ j) := by
    rw [additive_valuation_bundle_sum_ite, additive_valuation_bundle_sum_ite]
    exact e.sum_comp (fun g => if σ g = j then u i g else 0)
  rw [is_efx_goods_iff_bundle_totals, is_efx_goods_iff_bundle_totals]
  constructor
  · intro h i j hij g hg
    have hh := h i j hij (e.symm g) (by simpa using hg)
    simpa only [hval, e.apply_symm_apply] using hh
  · intro h i j hij g hg
    simpa only [hval] using h i j hij (e g) hg
