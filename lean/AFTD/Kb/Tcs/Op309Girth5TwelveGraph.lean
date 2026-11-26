import AFTD.Prelude

/-!
# op309_girth5_twelve_graph

Topic: graphs   Node: 96e7c52602d9

Provenance: helper lemma. OP-309; girth-five fixed-P3 obstruction, experiments 41671, 41673, 41674, 41678 and 41684.

The explicit twelve-vertex simple graph used for the fixed-P3 obstruction.
-/

def op309_girth5_twelve_graph : SimpleGraph (Fin 12) := {
  Adj := fun u v => (u.val,v.val) ∈ ([(0,5), (0,7), (0,8), (1,6), (1,7), (1,11), (2,6), (2,8), (2,10), (3,7), (3,9), (3,10), (4,8), (4,9), (4,11), (5,10), (5,11), (6,9)] : List (ℕ × ℕ)) ∨ (v.val,u.val) ∈ ([(0,5), (0,7), (0,8), (1,6), (1,7), (1,11), (2,6), (2,8), (2,10), (3,7), (3,9), (3,10), (4,8), (4,9), (4,11), (5,10), (5,11), (6,9)] : List (ℕ × ℕ))
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro u; fin_cases u <;> decide⟩
}
