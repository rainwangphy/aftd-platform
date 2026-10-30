import AFTD.Prelude
import AFTD.Kb.Tcs.ParallelMwAlpha
import AFTD.Kb.Tcs.ParallelMwStar
import AFTD.Kb.Tcs.ParallelMwTau

/-!
# parallel_mw_ratio

Topic: combinatorics   Node: 0fd34c2ed3fe

Provenance: formalization of a published result. Source: arXiv:2610.27706, Eq. (5)

For natural numbers n (implicit) and r, and q : Fin n → ℕ, parallel_mw_ratio r q is the real number defined by (parallel_mw_alpha n r * parallel_mw_star r q) / (parallel_mw_tau r q) ^ 2.
-/

/-- The multiplicative Merino-Welsh ratio of a partition matroid truncation. -/
noncomputable def parallel_mw_ratio {n : ℕ} (r : ℕ) (q : Fin n → ℕ) : ℝ := (parallel_mw_alpha n r * parallel_mw_star r q) / (parallel_mw_tau r q) ^ 2
