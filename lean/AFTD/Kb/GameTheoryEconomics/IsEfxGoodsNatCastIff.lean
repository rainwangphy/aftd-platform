import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuationEraseOfMem
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_efx_goods_nat_cast_iff

Topic: fair_division   Node: 37aca9cf5ecb

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01.

For natural-number item values, EFX after casting values to the reals is equivalent to all natural-number inequalities comparing each foreign total to the own total plus the value of any removed foreign good.
-/

open Function Finset

theorem is_efx_goods_nat_cast_iff {m n : ℕ} (v : Fin n → Fin m → ℕ) (σ : Fin m → Fin n) :
    is_efx_goods (fun i g => (v i g : ℝ)) σ ↔
      ∀ i j : Fin n, i ≠ j → ∀ g ∈ bundle_of σ j,
        (∑ h ∈ bundle_of σ j, v i h) ≤ (∑ h ∈ bundle_of σ i, v i h) + v i g := by
  constructor
  · intro h i j hij g hg
    have hh := h i j hij g hg
    rw [additive_valuation_erase_of_mem _ _ _ hg] at hh
    have h' := sub_le_iff_le_add.mp hh
    dsimp [additive_valuation] at h'
    exact_mod_cast h'
  · intro h i j hij g hg
    rw [additive_valuation_erase_of_mem _ _ _ hg]
    apply sub_le_iff_le_add.mpr
    have hh := h i j hij g hg
    dsimp [additive_valuation]
    exact_mod_cast hh
