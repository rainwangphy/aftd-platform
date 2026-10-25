import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianNoPerfectOfShapeBound
import AFTD.Kb.Tcs.MondrianPrimePowerShapeBound
import AFTD.Kb.Tcs.MondrianFactorShapes

/-!
# mondrian_no_perfect_prime_power

Topic: combinatorics   Node: eeada0268ca2

Provenance: formalization of a published result. Source: arXiv:2007.09639, Theorem 4.1(ii): no perfect partition for a square of prime-power side length; formalized in the cell-based definitions of arXiv:2610.19193, Section 1.

No square whose integer side length is a prime power has a perfect admissible partition.
-/

theorem mondrian_no_perfect_prime_power (p e : ℕ) (hp : Nat.Prime p) :
    ¬ ∃ P, mondrian_is_partition (p ^ e) P ∧ mondrian_defect P = 0 := by
  apply mondrian_no_perfect_of_shape_bound
  intro k A hk hA heq
  have hcard := mondrian_prime_power_shape_bound p e k A hp hk hA heq
  have hlt := Nat.factorization_lt p (by omega : k ≠ 0)
  exact lt_of_le_of_lt hcard hlt
