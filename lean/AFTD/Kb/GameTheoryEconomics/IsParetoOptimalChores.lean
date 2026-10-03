import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ParetoDominatesChores

/-!
# is_pareto_optimal_chores

Topic: fair_division   Node: 5303994d1c2d

An allocation of chores is Pareto optimal if no allocation Pareto-dominates it.
-/

/-- Pareto optimality for chores (arXiv:2608.16130, Def. 2.4): no (integral) allocation Pareto-dominates `σ`. -/
def is_pareto_optimal_chores {m n : ℕ} (c : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop :=
  ¬ ∃ τ, pareto_dominates_chores c τ σ
