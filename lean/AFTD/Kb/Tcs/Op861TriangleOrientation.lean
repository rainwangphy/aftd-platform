import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op861_triangle_orientation

Topic: graphs   Node: 9273f844ef46

Provenance: helper lemma. Triangle orientation model for the exponent-three construction of op861_ternary_tournament_sqrt_core_cover.

Given an abelian group equipped with a linear order and a Boolean choice for each finite set, return true for the edge from distinct x to y exactly when the choice on {x,y,−x−y} agrees with the cyclic order x,y,−x−y induced by the linear order.
-/

def op861_triangle_orientation (α : Type*) [AddCommGroup α] [DecidableEq α]
    [LinearOrder α] (turn : Finset α → Bool) (x y : α) : Bool := decide (x ≠ y ∧ (turn {x, y, -x-y} = true ↔
      ((x < y ∧ y < -x-y) ∨ (y < -x-y ∧ -x-y < x) ∨ (-x-y < x ∧ x < y))))
