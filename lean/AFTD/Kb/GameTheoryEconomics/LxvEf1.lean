import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LxvValues
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# lxv_ef1

Topic: fair_division   Node: 5ae0fe7d4779

Boolean EF1 check for allocations in the instance lxv_values.
-/

/-- Integer EF1 check for the instance `lxv_values`. -/
def lxv_ef1 (a : Fin 6 → Fin 4) : Bool :=
  (List.finRange 4).all fun i => (List.finRange 4).all fun j =>
    decide (lxv_val a i j ≤ lxv_val a i i) ||
      (List.finRange 6).any fun g => decide (a g = j) && decide (lxv_val a i j ≤ lxv_val a i i + lxv_values i g)
