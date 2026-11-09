import AFTD.Prelude

/-!
# gcd_self_add_five

Topic: elementary_number_theory   Node: 3f69397a0b81

Provenance: helper lemma. arXiv:2611.05623 Theorem 3.3 proof -- Partitions with designated summands: k-tuples and their congruences

For any natural number k, the greatest common divisor of k and k + 5 divides 5.
-/

/-- The gcd of k and k + 5 divides 5 for any natural number k. -/
theorem gcd_self_add_five (k : ℕ) : Nat.gcd k (k + 5) ∣ 5 := by
  rw [Nat.gcd_self_add_right]
  exact Nat.gcd_dvd_right k 5
