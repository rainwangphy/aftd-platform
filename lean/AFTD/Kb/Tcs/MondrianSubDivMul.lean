import AFTD.Prelude

/-!
# mondrian_sub_div_mul

Topic: combinatorics   Node: 17448850bb2a

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

For x at most y and positive a dividing y minus x, the quotient-coordinate difference multiplied by a is y minus x.
-/

theorem mondrian_sub_div_mul (a x y : ℕ) (ha : 0 < a) (hxy : x ≤ y)
    (hd : a ∣ y - x) : a * (y / a - x / a) = y - x := by
  obtain ⟨d, hd⟩ := hd
  have hy : y = x + a * d := by omega
  rw [hy, Nat.add_mul_div_left _ _ ha]
  simp
