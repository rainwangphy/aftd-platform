import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8U

/-!
# poc8_val

Topic: fair_division   Node: 3d7186d126c0

The total u-value of the vertex set selected by P, computed by a fold.
-/

/-- Total `u`-value of the vertices selected by `P`. -/
def poc8_val (P : Fin 8 → Bool) : ℕ :=
  (List.finRange 8).foldr (fun v acc => (if P v then poc8_u v else 0) + acc) 0
