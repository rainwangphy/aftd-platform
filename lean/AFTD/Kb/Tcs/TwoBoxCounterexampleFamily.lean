import AFTD.Prelude
import AFTD.Kb.Tcs.ExpectedUtilityDusLeOptDus
import AFTD.Kb.Tcs.OptDUS
import AFTD.Kb.Tcs.ExpectedUtilityDTD
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.TwoBoxFairValueDist
import AFTD.Kb.Tcs.TwoBoxRiskyValueDist
import AFTD.Kb.Tcs.TwoBoxDeadlineInst
import AFTD.Kb.Tcs.TwoBoxRiskyValueMean
import AFTD.Kb.Tcs.TwoBoxValidStopOfMemOne
import AFTD.Kb.Tcs.TwoBoxDtdAfterBoxZero
import AFTD.Kb.Tcs.TwoBoxPi01Valid
import AFTD.Kb.Tcs.TwoBoxPi01Dus
import AFTD.Kb.Tcs.TwoBoxDtdLeOne
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.PandoraDeadlineInstance

/-!
# two_box_counterexample_family

Topic: online_algorithms   Node: daadac0c3252

Provenance: helper lemma. step towards op182_deferred_to_deadline_beyond_half_against_stopping

For any integer `M > 1`, there exists a 2-box Pandora deadline instance such that `2 - 1 / M ≤ optDUS inst` and every valid policy `π` achieves `expectedUtilityDTD inst π ≤ 1`.
-/

/-- For any integer M > 1, there exists a 2-box instance with deadlines where optDUS is at least 2 - 1/M and every valid policy under DTD achieves expected utility at most 1. -/
theorem two_box_counterexample_family (M : ℕ) (hM : 1 < M) :
    ∃ inst : PandoraDeadlineInstance,
      2 - (1 : ℝ) / M ≤ optDUS inst ∧
      ∀ π : AdaptivePolicy inst.n, IsValidPolicy inst π → expectedUtilityDTD inst π ≤ 1 := by
  refine ⟨two_box_deadline_inst M hM, ?_, ?_⟩
  · calc 2 - (1 : ℝ) / M
        = expectedUtilityDUS (two_box_deadline_inst M hM)
            (AdaptivePolicy.openBox (0 : Fin 2) (fun _ => AdaptivePolicy.openBox (1 : Fin 2) (fun _ => AdaptivePolicy.stop))) :=
              (two_box_pi01_dus M hM).symm
      _ ≤ optDUS (two_box_deadline_inst M hM) :=
          expected_utility_dus_le_opt_dus _ _ (two_box_pi01_valid M hM)
  · intro π hπ
    exact two_box_dtd_le_one M hM π hπ
