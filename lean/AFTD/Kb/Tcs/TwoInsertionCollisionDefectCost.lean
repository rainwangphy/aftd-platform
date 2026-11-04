import AFTD.Prelude

/-!
# two_insertion_collision_defect_cost

Topic: information   Node: 0c2388a86028

Provenance: helper lemma. step towards op_999_two_insertion_collision_excess_sqrt_spacing_asymptotic

For naturals n and k, with q = (n-2)/(k+1) and r = (n-2) % (k+1), two_insertion_collision_defect_cost n k is the number 2kn + 2k^2 + n - 10k - 2 + (k+1-r) q^2 + r (q+1)^2: the excess over n.choose 2 of the two-insertion collision sum of the word consisting of blocks of length k+1 (k+1-r blocks of length q and r blocks of length q+1).
-/

/-- The cost term of the balanced-block family with block length k+1, i.e. the function being minimised inside two_insertion_collision_defect_envelope, extracted as a standalone definition. -/
def two_insertion_collision_defect_cost (n k : ℕ) : ℕ := let q := (n - 2) / (k + 1)
   let r := (n - 2) % (k + 1)
   2 * k * n + 2 * k ^ 2 + n - 10 * k - 2 + (k + 1 - r) * q ^ 2 + r * (q + 1) ^ 2
