import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance
import AFTD.Kb.Tcs.MultidimIsFeasibleSchedule
import AFTD.Kb.Tcs.OneshotDrfRate

/-!
# is_oneshot_drf_schedule

Topic: online_algorithms   Node: df1b15810801

Provenance: formalization of a published result. Source: arXiv:2611.07905 Tight Worst-Case Completion-Time Bounds for Dominant Resource Fairness, Section 2.2

A rate allocation x and completion time vector C satisfy is_oneshot_drf_schedule I x C for an instance I with D resources if multidim_is_feasible_schedule I x C holds and for every time t ≥ 0 and every job j, x j t equals oneshot_drf_rate I (Finset.univ.filter (fun k => t < C k)) j.
-/

/-- Predicate that a schedule follows the one-shot DRF allocation rule. -/
def is_oneshot_drf_schedule {D : ℕ} (I : MultidimInstance D) (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ) : Prop :=
  multidim_is_feasible_schedule I x C ∧
  ∀ (t : ℝ), 0 ≤ t →
    ∀ j, x j t = oneshot_drf_rate I (Finset.univ.filter (fun (k : Fin I.n) => t < C k)) j
