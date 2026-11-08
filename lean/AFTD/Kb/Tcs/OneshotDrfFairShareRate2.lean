import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance2

/-!
# oneshot_drf_fair_share_rate2

Topic: online_algorithms   Node: d4e248d5b038

Provenance: formalization of a published result. Source: arXiv:2611.07905 Sec. 2.2

For a two-resource multidimensional scheduling instance I and an active set of jobs A, the common fair-share rate is the supremum of lam >= 0 such that running every job j in A at rate min(u_j, lam) respects both resource capacities.
-/

/-- The common fair-share rate for an active set of jobs under one-shot DRF with two resources. -/
noncomputable def oneshot_drf_fair_share_rate2 (I : MultidimInstance2) (A : Finset (Fin I.n)) : ℝ :=
  sSup { lam : ℝ | 0 ≤ lam ∧ ∀ d : Fin 2, ∑ j ∈ A, I.a j d * min (I.u j) lam ≤ 1 }
