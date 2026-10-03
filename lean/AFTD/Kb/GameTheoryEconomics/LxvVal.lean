import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LxvValues

/-!
# lxv_val

Topic: fair_division   Node: 15ce705b8342

Agent i's integer value for agent j's bundle under an allocation, in the instance lxv_values.
-/

/-- Agent `i`'s integer value for the bundle of agent `j` under `a` in the instance `lxv_values`. -/
def lxv_val (a : Fin 6 → Fin 4) (i j : Fin 4) : ℕ :=
  (if a 0 = j then lxv_values i 0 else 0) + (if a 1 = j then lxv_values i 1 else 0) +
  (if a 2 = j then lxv_values i 2 else 0) + (if a 3 = j then lxv_values i 3 else 0) +
  (if a 4 = j then lxv_values i 4 else 0) + (if a 5 = j then lxv_values i 5 else 0)
