import AFTD.Prelude

/-!
# op1370_two_rank_edge_adjugate_numerator

Topic: combinatorics   Node: 4fcfbfd875f9

Provenance: helper lemma.

The adjugate numerator for the two-element adjacent-rank matrix is minus one.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_two_rank_edge_adjugate_numerator
    {K : Type*} [CommRing K] (a b s : K) (hs : s * s = 1) :
    (fun _ : Fin 2 => (1 : K)) ⬝ᵥ
      ((Matrix.adjugate !![a + s, a - b; -s, b - s]).mulVec ![s, -s]) = -1 := by
  rw [Matrix.adjugate_fin_two_of]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, one_mul, neg_neg]
  calc
    ((b - s) * s + (-(a - b)) * (-s)) +
        (s * s + (a + s) * (-s)) = -(s * s) := by ring
    _ = -1 := by rw [hs]
