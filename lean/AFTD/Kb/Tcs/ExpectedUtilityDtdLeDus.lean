import AFTD.Prelude
import AFTD.Kb.Tcs.ExpectedUtilityDTD
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# expected_utility_dtd_le_dus

Topic: online_algorithms   Node: 6f72e7d18c08

Provenance: helper lemma. arXiv:2610.13775 Sec. 2.1

For every Pandora's problem instance with deadlines `inst : PandoraDeadlineInstance` and every adaptive policy `π : AdaptivePolicy inst.n`, the expected net utility under deferred-to-deadline commitment `expectedUtilityDTD inst π` is at most the expected net utility under deferred-until-stopping commitment `expectedUtilityDUS inst π`.
-/

/-- Expected net utility under deferred-to-deadline commitment is at most that under deferred-until-stopping commitment. -/
theorem expected_utility_dtd_le_dus (inst : PandoraDeadlineInstance) (π : AdaptivePolicy inst.n) :
    expectedUtilityDTD inst π ≤ expectedUtilityDUS inst π := by
  unfold expectedUtilityDTD expectedUtilityDUS
  have hfold : ∀ (t : ℕ) (history : List (Fin inst.n × ℝ)),
      List.foldl (fun acc bv => if t ≤ inst.deadline bv.1 then max acc bv.2 else acc) 0 history
      ≤ List.foldl (fun acc bv => max acc bv.2) 0 history := by
    intro t history
    suffices h : ∀ (acc1 acc2 : ℝ) (l : List (Fin inst.n × ℝ)), acc1 ≤ acc2 →
        List.foldl (fun acc bv => if t ≤ inst.deadline bv.1 then max acc bv.2 else acc) acc1 l
        ≤ List.foldl (fun acc bv => max acc bv.2) acc2 l from h 0 0 history le_rfl
    intro acc1 acc2 l
    induction l generalizing acc1 acc2 with
    | nil => intro h; exact h
    | cons bv rest ih =>
        intro hle
        apply ih
        by_cases hc : t ≤ inst.deadline bv.1
        · simp only [hc, if_true]
          exact max_le_max hle le_rfl
        · simp only [hc, if_false]
          exact le_trans hle (le_max_left _ _)
  have key : ∀ (a : AdaptivePolicy inst.n) (history : List (Fin inst.n × ℝ)),
      expectedUtilityDTD.aux inst history a ≤ expectedUtilityDUS.aux inst history a := by
    intro a
    induction a using AdaptivePolicy.rec with
    | stop =>
        intro history
        exact hfold history.length history
    | openBox b cont ih =>
        intro history
        rw [show expectedUtilityDTD.aux inst history (AdaptivePolicy.openBox b cont) = _ from rfl,
            show expectedUtilityDUS.aux inst history (AdaptivePolicy.openBox b cont) = _ from rfl]
        apply sub_le_sub_right
        apply Finset.sum_le_sum
        intro v hv
        exact mul_le_mul_of_nonneg_left (ih v ((b, v) :: history)) ((inst.dist b).prob_nonneg v hv)
  exact key π []
