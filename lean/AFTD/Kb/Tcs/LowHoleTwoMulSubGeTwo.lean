import AFTD.Prelude

/-!
# low_hole_two_mul_sub_ge_two

Topic: combinatorics   Node: 40d3956f9c3e

Provenance: helper lemma. scout/2610-22875-overtake-and-the-recursive-line-equality-for-second-order-z.md:552

For integers z_RL, z_2, and z_2A, if z_RL ≤ z_2 and z_2 < z_2A, then 2 ≤ 2 * (z_2A - z_RL).
-/

/-- If z_RL ≤ z_2 and z_2 < z_2A, then 2 * (z_2A - z_RL) is at least 2. -/
theorem low_hole_two_mul_sub_ge_two (z_RL z_2 z_2A : ℤ)
    (hle : z_RL ≤ z_2) (hgt : z_2 < z_2A) :
    2 ≤ 2 * (z_2A - z_RL) := by
  omega
