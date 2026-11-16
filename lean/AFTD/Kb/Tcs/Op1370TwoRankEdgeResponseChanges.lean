import AFTD.Prelude

/-!
# op1370_two_rank_edge_response_changes

Topic: combinatorics   Node: b7f5efb0d3ac

Provenance: helper lemma.

A nonzero change of one weight changes the two-element scalar response when the other weight is nonzero.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_two_rank_edge_response_changes
    {K : Type*} [Field K] (a b t : K) (hb : b ≠ 0) (ht : t ≠ 0)
    (_h0 : a * b - 1 ≠ 0) (_h1 : (a + t) * b - 1 ≠ 0) :
    (-1 : K) / (a * b - 1) ≠ (-1 : K) / ((a + t) * b - 1) := by
  intro h
  simp only [neg_div, one_div, neg_inj] at h
  have he : a * b - 1 = (a + t) * b - 1 := inv_injective h
  have hz : t * b = 0 := by linear_combination -he
  exact (mul_ne_zero ht hb) hz
