import AFTD.Prelude

/-!
# lxv_values

Topic: fair_division   Node: a8befe26f667

The integer values of the instance: 4 agents, 6 goods, each agent's values summing to 20.
-/

/-- The instance: four agents, six goods, integer values each summing to 20. -/
def lxv_values : Fin 4 → Fin 6 → ℕ :=
  ![![6, 2, 3, 6, 1, 2], ![1, 1, 0, 5, 5, 8], ![4, 0, 0, 2, 1, 13], ![1, 1, 0, 2, 2, 14]]
