import AFTD.Prelude
import AFTD.Kb.Tcs.SymmetricCounterexampleFunc
import AFTD.Kb.Tcs.SymmetricCounterexampleFuncEight

/-!
# symmetric_counterexample_func_eight_eq

Topic: combinatorics   Node: 8177122ff965

Provenance: helper lemma. arXiv:2611.06744, Section 1

The symmetric Boolean function symmetric_counterexample_func 8 on (Fin 8 → ZMod 2) equals symmetric_counterexample_func_eight.
-/

private lemma symmetric_counterexample_func_eight_eq_key (x : Fin 8 → ZMod 2) :
    symmetric_counterexample_func 8 x
      = 1 + (∑ s ∈ Finset.powersetCard 2 Finset.univ, ∏ i ∈ s, x i)
        + (∑ s ∈ Finset.powersetCard 4 Finset.univ, ∏ i ∈ s, x i) := by
  simp only [symmetric_counterexample_func]
  norm_num [Finset.sum_range_succ]

/-- Equivalence of symmetric_counterexample_func 8 with symmetric_counterexample_func_eight. -/
theorem symmetric_counterexample_func_eight_eq : symmetric_counterexample_func 8 = symmetric_counterexample_func_eight := by
  funext x
  rw [symmetric_counterexample_func_eight_eq_key]
  rfl
