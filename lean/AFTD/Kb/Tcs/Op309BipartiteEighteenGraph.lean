import AFTD.Prelude

/-!
# op309_bipartite_eighteen_graph

Topic: graphs   Node: 530350ff5ec9

Provenance: helper lemma. OP-309 maximum-uncovered obstruction; experiment 40636.

The explicit cubic bipartite girth-six graph on which every maximum-uncovered almost-star forest obstructs overlap peeling.
-/

def op309_bipartite_eighteen_graph : SimpleGraph (Fin 18) := { Adj := fun u v => ((u.val,v.val) ∈ ([(0,9),(0,10),(0,11),(1,9),(1,12),(1,13),(2,9),(2,15),(2,16),(3,10),(3,12),(3,17),(4,10),(4,14),(4,16),(5,11),(5,13),(5,14),(6,11),(6,15),(6,17),(7,12),(7,14),(7,15),(8,13),(8,16),(8,17)] : List (Nat × Nat))) ∨ ((v.val,u.val) ∈ ([(0,9),(0,10),(0,11),(1,9),(1,12),(1,13),(2,9),(2,15),(2,16),(3,10),(3,12),(3,17),(4,10),(4,14),(4,16),(5,11),(5,13),(5,14),(6,11),(6,15),(6,17),(7,12),(7,14),(7,15),(8,13),(8,16),(8,17)] : List (Nat × Nat))), symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩, loopless := ⟨by intro v; fin_cases v <;> decide⟩ }
