import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianFactorShapes

/-!
# mondrian_mem_factor_shapes

Topic: combinatorics   Node: 605542217b4b

Provenance: helper lemma. arXiv:2610.19193, Section 1, and arXiv:2311.02385, Section 3 (available integer dimension pairs); helper for OP-280 and mondrian_no_perfect_partition.

A dimension pair belongs to the available shape set exactly when its product is the nonzero area A, its first dimension is at most its second, and its second is at most n.
-/

theorem mondrian_mem_factor_shapes (n A : ℕ) (d : ℕ × ℕ) :
    d ∈ mondrian_factor_shapes n A ↔
      d.1 * d.2 = A ∧ A ≠ 0 ∧ d.1 ≤ d.2 ∧ d.2 ≤ n := by
  simp only [mondrian_factor_shapes, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
  tauto
