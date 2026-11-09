import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsWefxGoods
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_wefx_goods_unit_weights_iff_is_efx_goods

Topic: fair_division   Node: 3985258f0907

Provenance: helper lemma. arXiv:2305.16081, Def. 3

When all agents have unit entitlements, weighted EFX is equivalent to standard unweighted EFX.
-/

/-- Weighted EFX with all entitlements equal to 1 coincides with standard EFX. -/
lemma is_wefx_goods_unit_weights_iff_is_efx_goods {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) :
    is_wefx_goods (fun _ => 1) u σ ↔ is_efx_goods u σ := by
  simp [is_wefx_goods, is_efx_goods]
