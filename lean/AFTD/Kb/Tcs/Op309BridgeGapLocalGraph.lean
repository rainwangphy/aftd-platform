import AFTD.Prelude

/-!
# op309_bridge_gap_local_graph

Topic: graphs   Node: 0b6b77660499

Provenance: helper lemma. OP-309 bridge-tree gap construction, experiment 40778.

A seven-vertex cubic block with its one external bridge stub.
-/

def op309_bridge_gap_local_graph : SimpleGraph (Fin 8) := { Adj := fun u v => ((u.val,v.val) ∈ ([(0,4),(0,5),(0,6),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,6),(6,7)] : List (Nat × Nat))) ∨ ((v.val,u.val) ∈ ([(0,4),(0,5),(0,6),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,6),(6,7)] : List (Nat × Nat))), symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩, loopless := ⟨by intro v; fin_cases v <;> decide⟩ }
