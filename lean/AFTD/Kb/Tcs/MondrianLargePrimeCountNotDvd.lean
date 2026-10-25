import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianPrimeFirstExponentShapeBound
import AFTD.Kb.Tcs.MondrianPrimePowGap
import AFTD.Kb.Tcs.MondrianPrimeShapeBound

/-!
# mondrian_large_prime_count_not_dvd

Topic: combinatorics   Node: 7969e1402c58

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

If enough distinct shapes of a common area fit in a c times p to the e square to account for its area, a prime p greater than c cannot divide the required tile count.
-/

theorem mondrian_large_prime_count_not_dvd (c p e k A : ℕ) (hc : 0 < c)
    (hp : Nat.Prime p) (hpc : c < p) (hk : 0 < k) (hA : 0 < A)
    (heq : k * A = (c * p ^ e) ^ 2)
    (hcard : k ≤ (mondrian_factor_shapes (c * p ^ e) A).card) : ¬ p ∣ k := by
  intro hpk
  have hr := (hp.dvd_iff_one_le_factorization (Nat.ne_of_gt hk)).mp hpk
  by_cases hr1 : k.factorization p = 1
  · have hbound := mondrian_prime_first_exponent_shape_bound c p e k A hc hp hpc hk hA heq hr1
    have hpkle := Nat.le_of_dvd hk hpk
    omega
  · have hbound := mondrian_prime_shape_bound c p e k A hc hp hpc hk hA heq
    have hgap := mondrian_prime_pow_gap c p (k.factorization p) hp.two_le hpc (by omega)
    have hpow := Nat.ordProj_le p (Nat.ne_of_gt hk)
    omega
