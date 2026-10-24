import AFTD.Prelude
import AFTD.Kb.Tcs.TwoBoxDeadlineInst
import AFTD.Kb.Tcs.TwoBoxRiskyValueMean
import AFTD.Kb.Tcs.TwoBoxValidStopOfMemOne
import AFTD.Kb.Tcs.TwoBoxDtdAfterBoxZero
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.TwoBoxRiskyValueDist
import AFTD.Kb.Tcs.TwoBoxFairValueDist
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.ExpectedUtilityDTD
import AFTD.Kb.Tcs.IsValidPolicyAux
import AFTD.Kb.Tcs.IsValidPolicy

/-!
# two_box_dtd_le_one

Topic: online_algorithms   Node: 316f39870f5c

Provenance: helper lemma. step towards two_box_counterexample_family

Under deferred-to-deadline commitment, every valid policy on the two-box instance gets expected utility at most 1.
-/

/-- Every valid policy achieves DTD expected utility at most 1 on the two-box instance. -/
theorem two_box_dtd_le_one (M : ℕ) (hM : 1 < M) (π : AdaptivePolicy 2)
    (hπ : IsValidPolicy (two_box_deadline_inst M hM) π) :
    expectedUtilityDTD (two_box_deadline_inst M hM) π ≤ 1 := by
  cases π with
  | stop => simp [expectedUtilityDTD, expectedUtilityDTD.aux]
  | openBox b cont =>
    show expectedUtilityDTD.aux (two_box_deadline_inst M hM) [] (AdaptivePolicy.openBox b cont) ≤ 1
    unfold IsValidPolicy at hπ
    rw [IsValidPolicyAux.eq_def] at hπ
    obtain ⟨hb, hd, hv⟩ := hπ
    simp only [expectedUtilityDTD.aux]
    by_cases hb0 : b = 0
    · rw [if_pos hb0]
      simp only [two_box_fair_value_dist, Finset.sum_singleton]
      have hzero : IsValidPolicyAux (two_box_deadline_inst M hM) rfl [(0 : Fin 2)] (cont 1) := by
        subst hb0
        have h := hv 1 (by simp [two_box_fair_value_dist])
        simpa using h
      have hle := two_box_dtd_after_box_zero M hM (cont 1) hzero
      subst hb0
      simpa using hle
    · rw [if_neg hb0]
      have hb1 : b = 1 := by
        fin_cases b
        · exact absurd rfl hb0
        · rfl
      subst hb1
      have hbound : ∀ x ∈ (two_box_risky_value_dist M hM).support,
          expectedUtilityDTD.aux (two_box_deadline_inst M hM) [((1 : Fin 2), x)] (cont x) ≤ x := by
        intro x hx
        have hvalid : IsValidPolicyAux (two_box_deadline_inst M hM) rfl [(1 : Fin 2)] (cont x) := by
          have h := hv x (by simpa using hx)
          simpa using h
        have hstop := two_box_valid_stop_of_mem_one M hM [(1 : Fin 2)] (cont x) hvalid (by simp) (by simp)
        have hx0 : 0 ≤ x := (two_box_risky_value_dist M hM).val_nonneg x hx
        rw [hstop]
        simp only [expectedUtilityDTD.aux, List.length_cons, List.length_nil]
        simp [hx0]
      have hsum : ∑ x ∈ (two_box_risky_value_dist M hM).support,
          (two_box_risky_value_dist M hM).prob x *
            expectedUtilityDTD.aux (two_box_deadline_inst M hM) [((1 : Fin 2), x)] (cont x)
          ≤ ∑ x ∈ (two_box_risky_value_dist M hM).support,
              (two_box_risky_value_dist M hM).prob x * x := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hbound x hx) ((two_box_risky_value_dist M hM).prob_nonneg x hx)
      rw [two_box_risky_value_mean M hM] at hsum
      linarith
