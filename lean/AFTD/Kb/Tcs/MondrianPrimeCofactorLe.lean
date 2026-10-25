import AFTD.Prelude

/-!
# mondrian_prime_cofactor_le

Topic: combinatorics   Node: 511e3fd7fa32

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

When k times A is the area of a c times p to the e square with p greater than c, the p-free part of A is at most c squared.
-/

theorem mondrian_prime_cofactor_le (c p e k A : ℕ) (hc : 0 < c)
    (hp : Nat.Prime p) (hpc : c < p) (heq : k * A = (c * p ^ e) ^ 2) :
    A / p ^ (A.factorization p) ≤ c ^ 2 := by
  have hcnot : ¬ p ∣ c := Nat.not_dvd_of_pos_of_lt hc hpc
  have hnn : (c * p ^ e) ^ 2 = p ^ (2 * e) * c ^ 2 := by
    rw [Nat.mul_comm 2 e, pow_mul]
    ring
  have hnc : ((c * p ^ e) ^ 2) / p ^ (((c * p ^ e) ^ 2).factorization p) = c ^ 2 := by
    rw [hnn]
    exact Nat.ordCompl_pow_mul_of_not_dvd (2 * e) hp
      (fun hh => hcnot (hp.dvd_of_dvd_pow hh))
  have hdiv : A ∣ (c * p ^ e) ^ 2 := by rw [← heq]; exact dvd_mul_left A k
  have hh := Nat.ordCompl_dvd_ordCompl_of_dvd hdiv p
  rw [hnc] at hh
  exact Nat.le_of_dvd (pow_pos hc 2) hh
