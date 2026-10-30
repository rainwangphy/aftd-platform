import AFTD.Prelude
import AFTD.Kb.Tcs.ElemSymm

/-!
# parallel_mw_tau

Topic: combinatorics   Node: 05bab3197780

Provenance: formalization of a published result. Source: arXiv:2610.27706, Eq. (8)

For natural numbers n (implicit) and r, and q : Fin n → ℕ, parallel_mw_tau r q is the real number defined by elem_symm r (fun i => (q i : ℝ)).
-/

/-- The basis count tau = T(1,1) defined as the r-th elementary symmetric sum of q. -/
def parallel_mw_tau {n : ℕ} (r : ℕ) (q : Fin n → ℕ) : ℝ := elem_symm r (fun i => (q i : ℝ))
