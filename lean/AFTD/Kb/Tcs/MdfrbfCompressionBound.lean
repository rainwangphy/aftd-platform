import AFTD.Prelude

/-!
# mdfrbf_compression_bound

Topic: combinatorics   Node: 9cbe29bc08d0

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours

Arithmetic side condition of the compression step: if j ≥ 2, a ≥ 1, b ≥ 2 and j*a + (j-1)*b + 1 ≤ d, then j*a + (j-1)*(b-1) + 1 ≤ d - (j-1).
-/

/-- Arithmetic: the (a, b-1) bound at dimension d-(j-1) follows from the (a, b) bound at dimension d. -/
theorem mdfrbf_compression_bound (j a b d : ℕ) (hj : 2 ≤ j) (ha : 1 ≤ a) (hb : 2 ≤ b)
    (hd : j * a + (j - 1) * b + 1 ≤ d) :
    j * a + (j - 1) * (b - 1) + 1 ≤ d - (j - 1) := by
  have hb1 : 1 ≤ b := by omega
  have h1 : (j - 1) * (b - 1) + (j - 1) = (j - 1) * b := by
    conv_rhs => rw [show b = (b - 1) + 1 from (Nat.sub_add_cancel hb1).symm]
    rw [Nat.mul_add, Nat.mul_one]
  omega
