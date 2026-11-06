import AFTD.Prelude
import AFTD.Kb.Tcs.InImplicit

/-!
# row_col_le

Topic: combinatorics   Node: 4efb27eff233

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 2.1

For a finite diagram D : Finset (ℕ × ℕ) and cells u, v : ℕ × ℕ, row_col_le D u v holds if there is a reflexive-transitive chain of unit rightward steps ((r, c) to (r, c+1)) and downward steps ((r, c) to (r+1, c)) in the implicit closure InImplicit D connecting u to v.
-/

/-- The row-column preorder on a diagram D via paths of rightward and downward steps in the implicit closure. -/
def row_col_le (D : Finset (ℕ × ℕ)) (u v : ℕ × ℕ) : Prop := Relation.ReflTransGen (fun x y => InImplicit D x ∧ InImplicit D y ∧
  ((x.1 = y.1 ∧ x.2 + 1 = y.2) ∨ (x.1 + 1 = y.1 ∧ x.2 = y.2))) u v
