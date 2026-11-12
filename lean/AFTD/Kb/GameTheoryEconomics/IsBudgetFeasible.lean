import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_budget_feasible

Topic: fair_division   Node: 0cdc868c7197

Provenance: formalization of a published result. Source: arXiv:2611.12740 Section 2

An allocation of m items to n agents is budget-feasible under item sizes s and agent budgets B if the allocated bundles are pairwise disjoint and each agent i's bundle has total size at most B_i.
-/

/-- An allocation of m items to n agents is budget-feasible under item sizes s and budgets B. -/
def is_budget_feasible {m n : ℕ} (s : Fin m → ℝ) (B : Fin n → ℝ)
    (X : Fin n → Finset (Fin m)) : Prop := (Pairwise fun i j => Disjoint (X i) (X j)) ∧
    ∀ i : Fin n, additive_valuation s (X i) ≤ B i
