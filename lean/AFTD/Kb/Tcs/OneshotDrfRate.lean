import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance
import AFTD.Kb.Tcs.OneshotDrfFairShareRate

/-!
# oneshot_drf_rate

Topic: online_algorithms   Node: fab9fc464d39

Provenance: formalization of a published result. Source: arXiv:2611.07905 Tight Worst-Case Completion-Time Bounds for Dominant Resource Fairness, Equation (2)

For a multidimensional scheduling instance I with D resources, an active set of jobs A, and a job j, the one-shot DRF rate oneshot_drf_rate I A j is defined as min (I.u j) (oneshot_drf_fair_share_rate I A) if j ∈ A, and 0 otherwise.
-/

/-- Rate of a job under one-shot DRF. -/
noncomputable def oneshot_drf_rate {D : ℕ} (I : MultidimInstance D) (A : Finset (Fin I.n)) (j : Fin I.n) : ℝ :=
  if j ∈ A then min (I.u j) (oneshot_drf_fair_share_rate I A) else 0
