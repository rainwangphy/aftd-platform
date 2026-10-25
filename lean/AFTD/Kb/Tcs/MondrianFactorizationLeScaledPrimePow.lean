import AFTD.Prelude

/-!
# mondrian_factorization_le_scaled_prime_pow

Topic: combinatorics   Node: e72f5df8b93c

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

A positive integer at most c times p to the e has p-adic exponent at most e when the prime p exceeds c.
-/

theorem mondrian_factorization_le_scaled_prime_pow (c p e x : ℕ) (hp : Nat.Prime p)
    (hpc : c < p) (hx : 0 < x) (hxn : x ≤ c * p ^ e) :
    x.factorization p ≤ e := by
  have hpow : p ^ (x.factorization p) < p ^ (e + 1) := by
    calc
      p ^ (x.factorization p) ≤ x := Nat.ordProj_le p (Nat.ne_of_gt hx)
      _ ≤ c * p ^ e := hxn
      _ < p * p ^ e := Nat.mul_lt_mul_of_pos_right hpc (pow_pos hp.pos e)
      _ = p ^ (e + 1) := by rw [pow_succ, Nat.mul_comm]
  have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hpow
  omega
