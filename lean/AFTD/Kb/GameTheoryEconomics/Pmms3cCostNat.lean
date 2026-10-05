import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pmms3cCost

/-!
# pmms3c_cost_nat

Topic: fair_division   Node: 020e5bc44c8d

The cost to agent i of the set of chores {g : P g}, as a natural number.
-/

/-- Agent `i`'s total cost of the chores selected by `P`, computed by a fold for the kernel. -/
def pmms3c_cost_nat (i : Fin 3) (P : Fin 9 → Bool) : ℕ :=
  (List.finRange 9).foldr (fun g acc => (if P g then pmms3c_cost i g else 0) + acc) 0
