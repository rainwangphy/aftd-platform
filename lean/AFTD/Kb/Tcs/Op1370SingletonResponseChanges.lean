import AFTD.Prelude

/-!
# op1370_singleton_response_changes

Topic: combinatorics   Node: 8259e470a672

Provenance: helper lemma.

A nonzero change of the weight changes the singleton scalar response when its sign is nonzero.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_singleton_response_changes
    {K : Type*} [Field K] (a s t : K) (hs : s ≠ 0) (ht : t ≠ 0) :
    s / (a + s) ≠ s / ((a + t) + s) := by
  intro h
  simp only [div_eq_mul_inv] at h
  have hi : (a + s)⁻¹ = ((a + t) + s)⁻¹ := mul_left_cancel₀ hs h
  have he : a + s = (a + t) + s := inv_injective hi
  apply ht
  linear_combination -he
