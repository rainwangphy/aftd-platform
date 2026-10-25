import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianNoPerfectOfShapeBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# mondrian_no_perfect_six

Topic: combinatorics   Node: 0e74d9507895

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

The integer square of side six has no perfect admissible partition.
-/

theorem mondrian_no_perfect_six :
    ¬ ∃ P, mondrian_is_partition 6 P ∧ mondrian_defect P = 0 := by
  apply mondrian_no_perfect_of_shape_bound
  intro k A hk hA heq
  have hAtop : A ≤ 18 := by nlinarith
  have htest : ∀ d : Fin 19, (mondrian_factor_shapes 6 d.val).card ≤ 2 := by decide
  have hcard := htest ⟨A, by omega⟩
  change (mondrian_factor_shapes 6 A).card ≤ 2 at hcard
  by_cases hk2 : k = 2
  · have hA18 : A = 18 := by nlinarith
    subst k A
    decide
  · omega
