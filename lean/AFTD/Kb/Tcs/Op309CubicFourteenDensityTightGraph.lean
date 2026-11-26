import AFTD.Prelude

/-!
# op309_cubic_fourteen_density_tight_graph

Topic: graphs   Node: 48630116f682

Provenance: helper lemma. OP-309 uncovered-density tightness, experiment 40688.

A cubic girth-six graph with a dominating almost-star forest attaining the universal uncovered-vertex upper bound.
-/

def op309_cubic_fourteen_density_tight_graph : SimpleGraph (Fin 14) := { Adj := fun u v => ((u.val,v.val) ∈ ([(0,1),(0,5),(0,13),(1,2),(1,10),(2,3),(2,7),(3,4),(3,12),(4,5),(4,9),(5,6),(6,7),(6,11),(7,8),(8,9),(8,13),(9,10),(10,11),(11,12),(12,13)] : List (Nat × Nat))) ∨ ((v.val,u.val) ∈ ([(0,1),(0,5),(0,13),(1,2),(1,10),(2,3),(2,7),(3,4),(3,12),(4,5),(4,9),(5,6),(6,7),(6,11),(7,8),(8,9),(8,13),(9,10),(10,11),(11,12),(12,13)] : List (Nat × Nat))), symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩, loopless := ⟨by intro v; fin_cases v <;> decide⟩ }
