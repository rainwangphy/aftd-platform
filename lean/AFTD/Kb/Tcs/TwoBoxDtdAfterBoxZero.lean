import AFTD.Prelude
import AFTD.Kb.Tcs.TwoBoxDeadlineInst
import AFTD.Kb.Tcs.TwoBoxRiskyValueMean
import AFTD.Kb.Tcs.TwoBoxValidStopOfMemOne
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.TwoBoxRiskyValueDist
import AFTD.Kb.Tcs.TwoBoxFairValueDist
import AFTD.Kb.Tcs.IsValidPolicyAux
import AFTD.Kb.Tcs.ExpectedUtilityDTD

/-!
# two_box_dtd_after_box_zero

Topic: online_algorithms   Node: 8e9d3149fb72

Provenance: helper lemma. step towards two_box_counterexample_family

With the history `[(0, 1)]`, any valid policy has deferred-to-deadline expected utility at most 1.
-/

theorem two_box_dtd_after_box_zero_unfold (M : ℕ) (hM : 1 < M) (π : AdaptivePolicy 2) :
    expectedUtilityDTD (two_box_deadline_inst M hM) π
      = expectedUtilityDTD.aux (two_box_deadline_inst M hM) [] π := rfl

/-- After box 0 (value 1) has been opened, the DTD payoff of any valid policy is at most 1, because box 0 is expired by round 2 and box 1 has mean value 1. -/
theorem two_box_dtd_after_box_zero (M : ℕ) (hM : 1 < M) (π : AdaptivePolicy 2)
    (hπ : IsValidPolicyAux (two_box_deadline_inst M hM) rfl [(0 : Fin 2)] π) :
    expectedUtilityDTD.aux (two_box_deadline_inst M hM) [((0 : Fin 2), (1:ℝ))] π ≤ 1 := by
  cases π with
  | stop =>
    simp [expectedUtilityDTD.aux, two_box_deadline_inst]
  | openBox b cont =>
    rw [IsValidPolicyAux.eq_def] at hπ
    obtain ⟨hb, hd, hv⟩ := hπ
    simp only [List.mem_singleton, List.length_singleton] at hb hd
    have hb1 : b = (1 : Fin 2) := by
      fin_cases b
      · exact absurd rfl hb
      · rfl
    subst hb1
    simp only [Fin.isValue, expectedUtilityDTD.aux, two_box_deadline_inst]
    simp only [Fin.reduceEq, reduceIte]
    have hv' : ∀ v ∈ (two_box_risky_value_dist M hM).support,
        IsValidPolicyAux (two_box_deadline_inst M hM) rfl [(1 : Fin 2), 0] (cont v) := by
      simpa using hv
    have hbound : ∀ x ∈ (two_box_risky_value_dist M hM).support,
        expectedUtilityDTD.aux (two_box_deadline_inst M hM) [((1 : Fin 2), x), (0, 1)] (cont x) ≤ x := by
      intro x hx
      have hcont := two_box_valid_stop_of_mem_one M hM [(1 : Fin 2), 0] (cont x) (hv' x hx) (by simp) (by simp)
      have hx0 : 0 ≤ x := (two_box_risky_value_dist M hM).val_nonneg x hx
      rw [hcont]
      simp only [expectedUtilityDTD.aux, two_box_deadline_inst, List.length_cons, List.length_nil,
        Fin.isValue]
      simp [hx0]
    have hsum : ∑ x ∈ (two_box_risky_value_dist M hM).support,
        (two_box_risky_value_dist M hM).prob x *
          expectedUtilityDTD.aux (two_box_deadline_inst M hM) [((1 : Fin 2), x), (0, 1)] (cont x)
        ≤ ∑ x ∈ (two_box_risky_value_dist M hM).support,
            (two_box_risky_value_dist M hM).prob x * x := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hbound x hx) ((two_box_risky_value_dist M hM).prob_nonneg x hx)
    rw [two_box_risky_value_mean M hM] at hsum
    linarith
