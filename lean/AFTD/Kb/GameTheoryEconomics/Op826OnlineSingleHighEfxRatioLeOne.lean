import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineSingleHighEfxRatio
import AFTD.Kb.GameTheoryEconomics.HasOnlineSingleHighAlphaEfx

/-!
# op826_online_single_high_efx_ratio_le_one

Topic: fair_division   Node: 6aec73690a9d

Provenance: helper lemma. arXiv:2610.34625

For every real value ratio R, the online single-high EFX competitive ratio for three agents is at most 1.
-/

/-- The online single-high EFX competitive ratio for three agents is at most 1 for any valuation ratio R. -/
theorem op826_online_single_high_efx_ratio_le_one (R : ℝ) :
    online_single_high_efx_ratio R ≤ 1 := by
  unfold online_single_high_efx_ratio
  apply Real.sSup_le
  · intro x hx
    exact hx.2.1
  · exact zero_le_one
