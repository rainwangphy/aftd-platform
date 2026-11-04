import AFTD.Prelude

/-!
# sweep_query

Topic: combinatorial_games   Node: 02b6642fbad4

Provenance: formalization of a published result. Source: arXiv:2611.01281 Section 5, Eq. 4

For natural numbers M, N, r, and j, `sweep_query M N r j` is the finite subset (Finset (Fin M × Fin N)) of vertices p in Fin M × Fin N such that (p.1.val = r ∧ j ≤ p.2.val) ∨ (p.1.val = r + 1 ∧ p.2.val ≤ j).
-/

/-- The diagonal sweep query T_{r,j} on an M-by-N grid. -/
def sweep_query (M N : ℕ) (r j : ℕ) : Finset (Fin M × Fin N) :=
  Finset.univ.filter fun p => (p.1.val = r ∧ j ≤ p.2.val) ∨ (p.1.val = r + 1 ∧ p.2.val ≤ j)
