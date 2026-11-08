import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance2
import AFTD.Kb.Tcs.IsOneshotDrfSchedule2

/-!
# oneshot_drf_total_completion_time2

Topic: online_algorithms   Node: fe20895be96d

Provenance: formalization of a published result. Source: arXiv:2611.07905 Sec. 2.2

The total completion time oneshot_drf_total_completion_time2 I of one-shot DRF on a two-resource instance I is defined as sInf { s | ∃ (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ), is_oneshot_drf_schedule2 I x C ∧ s = ∑ j, C j }.
-/

/-- Total completion time attained by one-shot DRF on an instance with two resources. -/
noncomputable def oneshot_drf_total_completion_time2 (I : MultidimInstance2) : ℝ :=
  sInf { s | ∃ (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ), is_oneshot_drf_schedule2 I x C ∧ s = ∑ j, C j }
