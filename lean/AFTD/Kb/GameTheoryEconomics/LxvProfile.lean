import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LxvVal
import AFTD.Kb.GameTheoryEconomics.LxvValues

/-!
# lxv_profile

Topic: fair_division   Node: 479960cdfdfd

Integer leximin profile (sorted own-bundle values) of an allocation in the instance lxv_values.
-/

/-- Integer leximin profile for the instance `lxv_values`. -/
def lxv_profile (a : Fin 6 → Fin 4) : List ℕ :=
  (List.ofFn fun i => lxv_val a i i).insertionSort (· ≤ ·)
