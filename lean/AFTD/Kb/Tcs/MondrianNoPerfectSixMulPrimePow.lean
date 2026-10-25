import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianLargePrimeDescent
import AFTD.Kb.Tcs.MondrianNoPerfectSix

/-!
# mondrian_no_perfect_six_mul_prime_pow

Topic: combinatorics   Node: b90ebc1b17fa

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

For every prime p greater than six and every natural e, the square of side six times p to the e has no perfect admissible partition.
-/

theorem mondrian_no_perfect_six_mul_prime_pow (p e : ℕ)
    (hp : Nat.Prime p) (hpc : 6 < p) :
    ¬ ∃ P, mondrian_is_partition (6 * p ^ e) P ∧ mondrian_defect P = 0 := by
  intro hP
  exact mondrian_no_perfect_six
    (mondrian_large_prime_descent 6 p e (by decide) hp hpc hP)
