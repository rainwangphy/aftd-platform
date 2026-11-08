import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance
import AFTD.Kb.Tcs.IsOneshotDrfSchedule

/-!
# oneshot_drf_total_completion_time

Topic: online_algorithms   Node: b20b859c213c

Provenance: formalization of a published result. Source: arXiv:2611.07905 Tight Worst-Case Completion-Time Bounds for Dominant Resource Fairness, Section 2.2

The total completion time oneshot_drf_total_completion_time I of one-shot DRF on an instance I with D resources is defined as the real infimum sInf of the set of all s such that there exist x and C satisfying is_oneshot_drf_schedule I x C with s = ∑ j, C j.
-/

/-- Total completion time under one-shot DRF. -/
noncomputable def oneshot_drf_total_completion_time {D : ℕ} (I : MultidimInstance D) : ℝ :=
  sInf { s | ∃ (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ), is_oneshot_drf_schedule I x C ∧ s = ∑ j, C j }
