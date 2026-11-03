import AFTD.Prelude

/-!
# three_val_poly_eval_mem

Topic: combinatorics   Node: 9cab869775be

Provenance: helper lemma. arXiv:2610.39908, Proposition A.1 proof, Low-rank matrices with three prescribed off-diagonal values over F_p

In any commutative ring $K$, the polynomial $(x - a) * (x - b) * (x - c)$ evaluates to $0$ at any $x \in \{a, b, c\}$.
-/

/-- The polynomial (X - a)(X - b)(X - c) vanishes at each of a, b, c. -/
theorem three_val_poly_eval_mem {K : Type*} [CommRing K] (a b c x : K)
    (hx : x ∈ ({a, b, c} : Set K)) :
    (x - a) * (x - b) * (x - c) = 0 := by
  rcases hx with rfl | rfl | rfl <;> ring
