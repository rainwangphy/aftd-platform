import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pmms3cTree

/-!
# pmms3c_tree_get

Topic: fair_division   Node: caed28c98bbc

Lookup in the ternary tree: follow branch d_1, then d_2, and so on, and return the leaf reached.
-/

/-- The leaf reached by following the branch choices `ds`. -/
def pmms3c_tree_get : Pmms3cTree → List (Fin 3) → ℕ := fun t ds =>
  match t, ds with
  | .leaf w, _ => w
  | .node _ _ _, [] => 0
  | .node t0 t1 t2, d :: ds =>
    match d.val with
    | 0 => pmms3c_tree_get t0 ds
    | 1 => pmms3c_tree_get t1 ds
    | _ => pmms3c_tree_get t2 ds
