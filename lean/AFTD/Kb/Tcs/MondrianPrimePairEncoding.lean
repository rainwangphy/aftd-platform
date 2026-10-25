import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianFactorizationLeScaledPrimePow

/-!
# mondrian_prime_pair_encoding

Topic: combinatorics   Node: 0afee0a47164

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

For an equal-area factor pair fitting in a c times p to the e square with p greater than c, the p-adic exponent of its first side lies between e minus the p-adic exponent of k and e, and its complementary factor divides the p-free part of A.
-/

theorem mondrian_prime_pair_encoding (c p e k A x y : ℕ) (hc : 0 < c)
    (hp : Nat.Prime p) (hpc : c < p) (hk : 0 < k) (hA : 0 < A)
    (heq : k * A = (c * p ^ e) ^ 2) (hx : 0 < x) (hy : 0 < y)
    (hxn : x ≤ c * p ^ e) (hyn : y ≤ c * p ^ e) (hxy : x * y = A) :
    e - k.factorization p ≤ x.factorization p ∧ x.factorization p ≤ e ∧
      (x / p ^ (x.factorization p)) ∈ (A / p ^ (A.factorization p)).divisors := by
  have hcnot : ¬ p ∣ c := Nat.not_dvd_of_pos_of_lt hc hpc
  have hvals : k.factorization p + A.factorization p = 2 * e := by
    have hf := congrArg (fun z : ℕ => z.factorization p) heq
    rw [Nat.factorization_mul (Nat.ne_of_gt hk) (Nat.ne_of_gt hA), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_mul (Nat.ne_of_gt hc) (pow_ne_zero e hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hcnot,
      Nat.factorization_pow_self hp] at hf
    simpa using hf
  have hxval := mondrian_factorization_le_scaled_prime_pow c p e x hp hpc hx hxn
  have hyval := mondrian_factorization_le_scaled_prime_pow c p e y hp hpc hy hyn
  have hxyval : x.factorization p + y.factorization p = A.factorization p := by
    have hh := congrArg (fun z : ℕ => z.factorization p) hxy
    simpa only [Nat.factorization_mul (Nat.ne_of_gt hx) (Nat.ne_of_gt hy),
      Finsupp.add_apply] using hh
  refine ⟨by omega, hxval, Nat.mem_divisors.mpr ⟨?_, ?_⟩⟩
  · apply Nat.ordCompl_dvd_ordCompl_of_dvd _ p
    exact ⟨y, hxy.symm⟩
  · exact Nat.ne_of_gt (Nat.ordCompl_pos p (Nat.ne_of_gt hA))
