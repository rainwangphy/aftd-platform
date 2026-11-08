import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance2
import AFTD.Kb.Tcs.MultidimOpt2
import AFTD.Kb.Tcs.OneshotDrfTotalCompletionTime2

/-!
# oneshot_drf_competitive_ratio2

Topic: online_algorithms   Node: ecba604fb94d

Provenance: formalization of a published result. Source: arXiv:2611.07905 Sec. 5

The worst-case competitive ratio oneshot_drf_competitive_ratio2 is defined as sSup { ρ | ∃ I : MultidimInstance2, ρ = oneshot_drf_total_completion_time2 I / multidim_opt2 I }.
-/

/-- Worst-case competitive ratio of one-shot DRF for total completion time with two resources. -/
noncomputable def oneshot_drf_competitive_ratio2 : ℝ :=
  sSup { ρ | ∃ I : MultidimInstance2, ρ = oneshot_drf_total_completion_time2 I / multidim_opt2 I }
