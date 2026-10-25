import AFTD.Prelude

/-!
# mondrian_interval_div

Topic: combinatorics   Node: 719e59079dbe

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

An integer cell i belongs to the coordinatewise quotient of an interval precisely when the last cell of its a-block belongs to the original interval, for a positive.
-/

theorem mondrian_interval_div (a x y i : ℕ) (ha : 0 < a) :
    (x / a ≤ i ∧ i < y / a) ↔
      x ≤ a * (i + 1) - 1 ∧ a * (i + 1) - 1 < y := by
  have h1 : x / a ≤ i ↔ x < a * (i + 1) := by
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul ha, Nat.mul_comm]
  have h2 : i < y / a ↔ a * (i + 1) ≤ y := by
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le ha, Nat.mul_comm]
  rw [h1, h2]
  have hp : 0 < a * (i + 1) := Nat.mul_pos ha (by omega)
  omega
