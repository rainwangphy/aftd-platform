import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Op826EnvelopeAtTwo
import AFTD.Kb.GameTheoryEconomics.Op826OnlineSingleHighEfxRatioLeOne
import AFTD.Kb.GameTheoryEconomics.OnlineSingleHighEfxRatio

/-!
# op826_online_single_high_efx_upper_bound_two

Topic: fair_division   Node: 0c61e1d52a5d

Provenance: helper lemma. arXiv:2610.34625

For three agents and value ratio R = 2, the online single-high EFX competitive ratio is at most the conjectured envelope min (1 / floor(sqrt 2)) (ceil(sqrt 2) / 2).
-/

/-- The upper envelope bound holds at R = 2: online_single_high_efx_ratio 2 <= envelope(2). -/
theorem op826_online_single_high_efx_upper_bound_two :
    online_single_high_efx_ratio 2 ≤ min (1 / (⌊Real.sqrt (2 : ℝ)⌋ : ℝ)) ((⌈Real.sqrt (2 : ℝ)⌉ : ℝ) / (2 : ℝ)) := by
  rw [op826_envelope_at_two]
  exact op826_online_single_high_efx_ratio_le_one 2
