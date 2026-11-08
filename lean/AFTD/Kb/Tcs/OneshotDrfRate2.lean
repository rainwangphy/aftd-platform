import AFTD.Prelude
import AFTD.Kb.Tcs.OneshotDrfFairShareRate2
import AFTD.Kb.Tcs.MultidimInstance2

/-!
# oneshot_drf_rate2

Topic: online_algorithms   Node: 932fe9c5dd8e

Provenance: formalization of a published result. Source: arXiv:2611.07905 Sec. 2.2

For a two-resource multidimensional scheduling instance I, an active set of jobs A, and a job j, the one-shot DRF rate of j is min(u_j, lambda(A)) if j is in A, and 0 otherwise.
-/

/-- The rate assigned to a job under one-shot DRF given an active set. -/
noncomputable def oneshot_drf_rate2 (I : MultidimInstance2) (A : Finset (Fin I.n)) (j : Fin I.n) : ℝ :=
  if j ∈ A then min (I.u j) (oneshot_drf_fair_share_rate2 I A) else 0
