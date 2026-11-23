import AFTD.Prelude
import AFTD.Kb.Tcs.SymmetricBooleanDegreeDeficitMax

/-!
# symmetric_boolean_degree_deficit_max_le_self

Topic: algebraic_complexity   Node: 4bf948833988

Provenance: helper lemma. arXiv:2611.26446, Sec. 1.1

For every natural number $n$, the maximum degree deficit of nonconstant symmetric Boolean functions on $n$ variables is at most $n$.
-/

/-- The maximum degree deficit satisfies Δ(n) ≤ n. -/
theorem symmetric_boolean_degree_deficit_max_le_self (n : ℕ) : symmetric_boolean_degree_deficit_max n ≤ n := by
  unfold symmetric_boolean_degree_deficit_max
  apply Finset.sup_le
  intro F _
  split_ifs
  · exact Nat.sub_le _ _
  · exact Nat.zero_le _
