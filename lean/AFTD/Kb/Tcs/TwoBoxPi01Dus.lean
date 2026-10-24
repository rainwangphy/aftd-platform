import AFTD.Prelude
import AFTD.Kb.Tcs.TwoBoxDeadlineInst
import AFTD.Kb.Tcs.TwoBoxFairValueDist
import AFTD.Kb.Tcs.TwoBoxRiskyValueDist
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# two_box_pi01_dus

Topic: online_algorithms   Node: 48e4c179c0c0

Provenance: helper lemma. step towards two_box_counterexample_family

The DUS utility of the policy opening box 0 then box 1 is `2 - 1/M`.
-/

/-- Under deferred-until-stopping, opening box 0 then box 1 yields `2 - 1/M`: box 0's value 1 is never forgotten and box 1 adds mean `1/M · M = 1`. -/
theorem two_box_pi01_dus (M : ℕ) (hM : 1 < M) :
    expectedUtilityDUS (two_box_deadline_inst M hM)
      (AdaptivePolicy.openBox (0 : Fin 2) (fun _ => AdaptivePolicy.openBox (1 : Fin 2) (fun _ => AdaptivePolicy.stop)))
      = 2 - 1 / (M : ℝ) := by
  have hMgt1 : (1 : ℝ) < (M : ℝ) := Nat.one_lt_cast.mpr hM
  have h1M : (1 : ℝ) ≤ (M : ℝ) := le_of_lt hMgt1
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  have hne : (0 : ℝ) ≠ (M : ℝ) := ne_of_lt hMpos
  simp only [expectedUtilityDUS, expectedUtilityDUS.aux, two_box_deadline_inst]
  simp [two_box_fair_value_dist]
  simp only [two_box_risky_value_dist]
  rw [Finset.sum_pair hne]
  simp only [if_true, if_neg hne.symm]
  have hA : max (max 0 0) (1 : ℝ) = 1 := by norm_num
  have hB : max (max 0 (M : ℝ)) 1 = M := by rw [max_eq_right (le_of_lt hMpos), max_eq_left h1M]
  rw [hA, hB]
  have hinv : (M : ℝ) * (M : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hMpos)
  linarith
