import AFTD.Prelude

/-!
# sweep_candidate_bound

Topic: combinatorial_games   Node: 77a88902593f

Provenance: formalization of a published result. Source: arXiv:2611.01281 Section 5, Eq. 5

For natural numbers M, N, r, and j, `sweep_candidate_bound M N r j` is the finite subset (Finset (Fin M × Fin N)) of vertices p in Fin M × Fin N such that (p.1.val = r + 1 ∧ j < p.2.val) ∨ (r + 2 ≤ p.1.val).
-/

/-- The candidate set upper bound after a negative answer to sweep query T_{r,j}. -/
def sweep_candidate_bound (M N : ℕ) (r j : ℕ) : Finset (Fin M × Fin N) :=
  Finset.univ.filter fun p => (p.1.val = r + 1 ∧ j < p.2.val) ∨ (r + 2 ≤ p.1.val)
