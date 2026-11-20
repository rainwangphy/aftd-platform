import AFTD.Prelude

/-!
# op309_weighted_eight_graph

Topic: graphs   Node: 1a95ecff630c

Provenance: helper lemma. OP-309 weighted-four shortcut examined in IN-1099.

The explicit connected eight-vertex cubic graph used for the weighted-four selection obstruction.
-/

def op309_weighted_eight_graph : SimpleGraph (Fin 8) := { Adj := fun u v => ((u.val,v.val) ∈ ([(0,3),(0,4),(0,5),(1,4),(1,5),(1,6),(2,5),(2,6),(2,7),(3,6),(3,7),(4,7)] : List (Nat × Nat))) ∨ ((v.val,u.val) ∈ ([(0,3),(0,4),(0,5),(1,4),(1,5),(1,6),(2,5),(2,6),(2,7),(3,6),(3,7),(4,7)] : List (Nat × Nat))), symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩, loopless := ⟨by intro v; fin_cases v <;> decide⟩ }
