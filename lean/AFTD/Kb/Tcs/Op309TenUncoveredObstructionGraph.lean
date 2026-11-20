import AFTD.Prelude

/-!
# op309_ten_uncovered_obstruction_graph

Topic: graphs   Node: 6e627c451baa

Provenance: helper lemma. OP-309 uncovered-vertex selection; experiments 36551, 36556, 36558.

The explicit ten-vertex cubic graph used to test the number of uncovered vertices in a dominating almost-star forest.
-/

def op309_ten_uncovered_obstruction_graph : SimpleGraph (Fin 10) := { Adj := fun u v => ((u.val,v.val) ∈ ([(0,3),(0,6),(0,9),(1,4),(1,6),(1,8),(2,5),(2,6),(2,7),(3,7),(3,8),(4,7),(4,9),(5,8),(5,9)] : List (Nat × Nat))) ∨ ((v.val,u.val) ∈ ([(0,3),(0,6),(0,9),(1,4),(1,6),(1,8),(2,5),(2,6),(2,7),(3,7),(3,8),(4,7),(4,9),(5,8),(5,9)] : List (Nat × Nat))), symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩, loopless := ⟨by intro v; fin_cases v <;> decide⟩ }
