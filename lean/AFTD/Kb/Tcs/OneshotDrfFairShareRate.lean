import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance

/-!
# oneshot_drf_fair_share_rate

Topic: online_algorithms   Node: 68d7a4f715ac

Provenance: formalization of a published result. Source: arXiv:2611.07905 Tight Worst-Case Completion-Time Bounds for Dominant Resource Fairness, Equation (1)

For a multidimensional scheduling instance I with D resources and an active set of jobs A, the common fair-share rate oneshot_drf_fair_share_rate I A is the real supremum sSup of all lam ≥ 0 such that for every resource d : Fin D, the sum over j ∈ A of I.a j d * min (I.u j) lam is at most 1.
-/

/-- Common fair-share rate for an active set of jobs under DRF. -/
noncomputable def oneshot_drf_fair_share_rate {D : ℕ} (I : MultidimInstance D) (A : Finset (Fin I.n)) : ℝ :=
  sSup { lam : ℝ | 0 ≤ lam ∧ ∀ d : Fin D, ∑ j ∈ A, I.a j d * min (I.u j) lam ≤ 1 }
