import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_efx_goods_scale

Topic: fair_division   Node: da83a0d4cd2e

Provenance: helper lemma. step towards scaled_common_ratio_bivalued_efx_fpo_envyfreeable

Multiplying each agent's additive valuation vector by a positive constant c_i > 0 preserves and reflects whether an allocation is EFX.
-/

/-- The EFX property of an allocation is invariant under multiplying each agent's valuation vector by a positive constant. -/
theorem is_efx_goods_scale {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    is_efx_goods (fun i g => c i * u i g) σ ↔ is_efx_goods u σ := by
  have h : ∀ (i : Fin n) (S : Finset (Fin m)), additive_valuation (fun g => c i * u i g) S = c i * additive_valuation (u i) S := by
    intro i S
    simp [additive_valuation, Finset.mul_sum]
  unfold is_efx_goods
  constructor
  · intro H i j hij g hg
    have h1 := H i j hij g hg
    rw [h, h] at h1
    exact (mul_le_mul_iff_of_pos_left (hc i)).mp h1
  · intro H i j hij g hg
    have h1 := H i j hij g hg
    rw [h, h]
    exact (mul_le_mul_iff_of_pos_left (hc i)).mpr h1
