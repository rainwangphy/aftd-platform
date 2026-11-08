import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance2
import AFTD.Kb.Tcs.OneshotDrfRate2
import AFTD.Kb.Tcs.MultidimIsFeasibleSchedule2

/-!
# is_oneshot_drf_schedule2

Topic: online_algorithms   Node: cd2d59853b52

Provenance: formalization of a published result. Source: arXiv:2611.07905 Sec. 2.2

A schedule (x, C) satisfies is_oneshot_drf_schedule2 I x C for a two-resource instance I if multidim_is_feasible_schedule2 I x C holds and for every time t ≥ 0 and every job j, x j t equals oneshot_drf_rate2 I applied to the set of jobs k with t < C k.
-/

/-- Predicate for a schedule being executed according to one-shot DRF. -/
def is_oneshot_drf_schedule2 (I : MultidimInstance2) (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ) : Prop :=
  multidim_is_feasible_schedule2 I x C ∧
  ∀ (t : ℝ), 0 ≤ t →
    ∀ j, x j t = oneshot_drf_rate2 I (Finset.univ.filter (fun (k : Fin I.n) => t < C k)) j
