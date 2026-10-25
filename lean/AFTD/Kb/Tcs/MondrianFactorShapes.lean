import AFTD.Prelude

/-!
# mondrian_factor_shapes

Topic: combinatorics   Node: 87bd9b763812

Provenance: helper lemma. arXiv:2610.19193, Section 1, and arXiv:2311.02385, Section 3 (available integer dimension pairs); helper for OP-280 and mondrian_no_perfect_partition.

The available unordered integer dimension pairs of positive area A that fit in an n-square, encoded in increasing order.
-/

def mondrian_factor_shapes (n A : ℕ) : Finset (ℕ × ℕ) :=
  A.divisorsAntidiagonal.filter (fun d => d.1 ≤ d.2 ∧ d.2 ≤ n)
