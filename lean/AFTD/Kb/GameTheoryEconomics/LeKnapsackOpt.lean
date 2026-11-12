import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackOpt
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# le_knapsack_opt

Topic: fair_division   Node: 0650190ae0a0

Provenance: helper lemma. arXiv:2611.12740 Section 3.1

Every budget-feasible subset S of C achieves value at most OPT(C).
-/

/-- Every budget-feasible subset of C achieves value at most OPT(C). -/
theorem le_knapsack_opt {m : ℕ} (v : Fin m → ℝ) (s : Fin m → ℝ) (b : ℝ)
    (C : Finset (Fin m)) (S : Finset (Fin m)) (hSC : S ⊆ C)
    (hSb : additive_valuation s S ≤ b) :
    additive_valuation v S ≤ knapsack_opt v s b C := by
  classical
  rw [knapsack_opt]
  haveI : Finite {T : Finset (Fin m) // T ⊆ C ∧ additive_valuation s T ≤ b} := by
    infer_instance
  exact Finite.le_ciSup
    (fun T : {T : Finset (Fin m) // T ⊆ C ∧ additive_valuation s T ≤ b} =>
      additive_valuation v T.val)
    ⟨S, hSC, hSb⟩
