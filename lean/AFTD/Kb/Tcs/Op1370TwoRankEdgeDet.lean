import AFTD.Prelude

/-!
# op1370_two_rank_edge_det

Topic: combinatorics   Node: c7e318125426

Provenance: helper lemma.

The determinant of the two-element adjacent-rank matrix is the product of its weights minus one.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_two_rank_edge_det
    {K : Type*} [CommRing K] (a b s : K) (hs : s * s = 1) :
    Matrix.det !![a + s, a - b; -s, b - s] = a * b - 1 := by
  rw [Matrix.det_fin_two_of]
  calc
    (a + s) * (b - s) - (a - b) * (-s) = a * b - s * s := by ring
    _ = a * b - 1 := by rw [hs]
