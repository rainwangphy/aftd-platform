import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDivisorsCardLeTwoMulOfLeSq
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianOrderedPrimeShapeBound
import AFTD.Kb.Tcs.MondrianOrderedShapeHalf
import AFTD.Kb.Tcs.MondrianPrimeCofactorLe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_prime_shape_bound

Topic: combinatorics   Node: f0c938c06afa

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

If k times A is the area of a c times p to the e square and p exceeds c, at most c times one plus the p-adic exponent of k unordered shapes of area A fit in the square.
-/

theorem mondrian_prime_shape_bound (c p e k A : ℕ) (hc : 0 < c)
    (hp : Nat.Prime p) (hpc : c < p) (hk : 0 < k) (hA : 0 < A)
    (heq : k * A = (c * p ^ e) ^ 2) :
    (mondrian_factor_shapes (c * p ^ e) A).card ≤ (k.factorization p + 1) * c := by
  have h1 := mondrian_ordered_shape_half (c * p ^ e) A
  have h2 := mondrian_ordered_prime_shape_bound c p e k A hc hp hpc hk hA heq
  have h3 := mondrian_prime_cofactor_le c p e k A hc hp hpc heq
  have h4 := mondrian_divisors_card_le_two_mul_of_le_sq (A / p ^ (A.factorization p)) c h3
  have h5 := Nat.mul_le_mul_left (k.factorization p + 1) h4
  nlinarith
