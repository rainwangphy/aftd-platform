import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ParetoDominatesGoods

/-!
# is_pareto_optimal_goods

Topic: fair_division   Node: aceb3c64aeac

An allocation of goods is Pareto optimal if no allocation Pareto-dominates it.
-/

/-- An allocation of goods is Pareto optimal if no allocation Pareto-dominates it. -/
def is_pareto_optimal_goods {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop :=
  ¬ ∃ τ, pareto_dominates_goods u τ σ
