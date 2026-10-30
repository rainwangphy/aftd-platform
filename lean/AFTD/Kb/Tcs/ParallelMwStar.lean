import AFTD.Prelude
import AFTD.Kb.Tcs.ElemSymm

/-!
# parallel_mw_star

Topic: combinatorics   Node: b09cbe4adef1

Provenance: formalization of a published result. Source: arXiv:2610.27706, Eq. (11)

For natural numbers n (implicit) and r, and q : Fin n → ℕ, parallel_mw_star r q is the real number defined by the sum for k from 0 to n of (if k < r then (-1 : ℝ) ^ (r - k) else 1) * elem_symm k (fun i => (2 : ℝ) ^ (q i) - 1).
-/

/-- The Tutte evaluation star = T(0,2) defined in terms of elementary symmetric sums. -/
noncomputable def parallel_mw_star {n : ℕ} (r : ℕ) (q : Fin n → ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), (if k < r then (-1 : ℝ) ^ (r - k) else 1) *
    elem_symm k (fun i => (2 : ℝ) ^ (q i) - 1)
