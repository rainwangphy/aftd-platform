import AFTD.Prelude

/-!
# mondrian_sorted_pairs_eq_of_shared

Topic: combinatorics   Node: a46e9dec41c0

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

Two increasing positive factor pairs of the same nonzero area that share a side length are equal.
-/

theorem mondrian_sorted_pairs_eq_of_shared (x y : ℕ × ℕ) (A : ℕ)
    (hA : 0 < A) (hxp : x.1 * x.2 = A) (hyp : y.1 * y.2 = A)
    (hxo : x.1 ≤ x.2) (hyo : y.1 ≤ y.2)
    (h : x.1 = y.1 ∨ x.1 = y.2 ∨ x.2 = y.1 ∨ x.2 = y.2) : x = y := by
  have hx1 : 0 < x.1 := Nat.pos_of_mul_pos_right (by omega : 0 < x.1 * x.2)
  have hx2 : 0 < x.2 := Nat.pos_of_mul_pos_left (by omega : 0 < x.1 * x.2)
  rcases h with h | h | h | h
  · have h2 : x.2 = y.2 := by
      apply Nat.eq_of_mul_eq_mul_left hx1
      rw [hxp, h, hyp]
    exact Prod.ext h h2
  · have h2 : x.2 = y.1 := by
      apply Nat.eq_of_mul_eq_mul_left hx1
      calc
        x.1 * x.2 = A := hxp
        _ = y.2 * y.1 := by rw [Nat.mul_comm, hyp]
        _ = x.1 * y.1 := by rw [h]
    apply Prod.ext <;> omega
  · have h1 : x.1 = y.2 := by
      apply Nat.eq_of_mul_eq_mul_right hx2
      calc
        x.1 * x.2 = A := hxp
        _ = y.2 * y.1 := by rw [Nat.mul_comm, hyp]
        _ = y.2 * x.2 := by rw [h]
    apply Prod.ext <;> omega
  · have h1 : x.1 = y.1 := by
      apply Nat.eq_of_mul_eq_mul_right hx2
      rw [hxp, h, hyp]
    exact Prod.ext h1 h
