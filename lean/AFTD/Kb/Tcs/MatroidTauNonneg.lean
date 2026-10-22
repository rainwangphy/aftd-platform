import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidTau
import AFTD.Kb.Tcs.MatroidTutteEval

/-!
# matroid_tau_nonneg

Topic: combinatorics   Node: 442aa3644e54

Provenance: helper lemma. step towards matroid_min_counterexample_parallel_or_series

For every finite matroid M, the Tutte evaluation T_M(1,1) is non-negative. (This is the number of bases of M, but here it is just the trivial positivity of the defining power sum.)
-/

/-- The Tutte evaluation T_M(1,1) is non-negative: in its defining powerset sum every summand is (1-1)^a * (1-1)^b = 0^a * 0^b, a product of non-negative reals. -/
theorem matroid_tau_nonneg {α : Type*} (M : Matroid α) [M.Finite] : 0 ≤ matroid_tau M := by
  unfold matroid_tau matroid_tutte_eval
  simp only [sub_self]
  apply Finset.sum_nonneg
  intro x hx
  positivity
