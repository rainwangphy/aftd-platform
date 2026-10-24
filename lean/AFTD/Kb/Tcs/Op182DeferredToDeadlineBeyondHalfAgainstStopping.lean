import AFTD.Prelude
import AFTD.Kb.Tcs.OptDUS
import AFTD.Kb.Tcs.ExpectedUtilityDTD
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.ExpectedUtilityDusLeOptDus
import AFTD.Kb.Tcs.TwoBoxCounterexampleFamily
import AFTD.Kb.Tcs.ArchimedeanRatioGtOne
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# op182_deferred_to_deadline_beyond_half_against_stopping

Topic: online_algorithms   Node: acf9e70198c1

Provenance: formalization of a published result. Source: arXiv:2610.13775 Sec. 5

Refutation of Open Problem OP-182 against the deferred-until-stopping benchmark: there does not exist any constant `c > 1/2` such that for every Pandora's problem instance with deadlines `inst : PandoraDeadlineInstance`, there exists a valid adaptive policy `π` satisfying `IsValidPolicy inst π` whose expected utility under deferred-to-deadline commitment `expectedUtilityDTD inst π` is at least `c * optDUS inst`.
-/

/-- Refutation of OP-182: deferred-to-deadline policies cannot achieve approximation ratio > 1/2 against deferred-until-stopping OPT. -/
theorem op182_deferred_to_deadline_beyond_half_against_stopping :
    ¬ (∃ c > (1 / 2 : ℝ), ∀ inst : PandoraDeadlineInstance,
        ∃ π : AdaptivePolicy inst.n, IsValidPolicy inst π ∧
          c * optDUS inst ≤ expectedUtilityDTD inst π) := by
  rintro ⟨c, hc, h_all⟩
  obtain ⟨M, hM, hM_ineq⟩ := archimedean_ratio_gt_one c hc
  obtain ⟨inst, h_opt, h_dtd⟩ := two_box_counterexample_family M hM
  obtain ⟨π, hπ_valid, hπ_bound⟩ := h_all inst
  have h_dtd_le_1 := h_dtd π hπ_valid
  have hc_pos : 0 < c := by linarith
  have h_c_opt : c * (2 - (1 : ℝ) / M) ≤ c * optDUS inst := by
    nlinarith
  linarith
