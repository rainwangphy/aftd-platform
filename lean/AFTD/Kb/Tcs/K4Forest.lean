import AFTD.Prelude

/-!
# k4_forest

Topic: combinatorics   Node: 7e69e75b8b40

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), proof of Theorem 1.1 (the graphic matroid M(K₄))

The independent sets of the cycle matroid of K₄, with the six edges numbered 01, 23, 02, 13, 03, 12 (so {0,1}, {2,3}, {4,5} are the pairs of opposite edges): the edge sets with at most three edges that are not a triangle.
-/

/-- Independent edge sets of `K₄`, edges numbered `0 = 01, 1 = 23, 2 = 02, 3 = 13, 4 = 03, 5 = 12` (so `{0,1}`, `{2,3}`, `{4,5}` are the opposite pairs): forests, i.e. at most three edges and not a triangle. -/
abbrev k4_forest (I : Finset (Fin 6)) : Prop :=
  I.card ≤ 3 ∧ I ≠ {0, 2, 5} ∧ I ≠ {0, 3, 4} ∧ I ≠ {1, 2, 4} ∧ I ≠ {1, 3, 5}
