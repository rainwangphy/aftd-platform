import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LxvValues

/-!
# lxv_instance

Topic: fair_division   Node: 78aafd546f1f

The real instance lxv_values / 20: nonnegative additive values summing to 1 for each agent.
-/

/-- The real instance: `lxv_values / 20`, so every agent's values are nonnegative and sum to 1. -/
noncomputable def lxv_instance : Fin 4 → Fin 6 → ℝ := fun i g => (lxv_values i g : ℝ) / 20
