import AFTD.Prelude

/-!
# op309_six_bipartite_maximum_graph

Topic: graphs   Node: e526741c1d3e

Provenance: helper lemma. OP-309 maximum-uncovered counterexample, experiments 40720 and 40722.

The six-vertex complete cubic bipartite graph used to refute maximum-uncovered selected-rich forest selection.
-/

def op309_six_bipartite_maximum_graph : SimpleGraph (Fin 6) := { Adj := fun u v => ((u.val,v.val) ∈ ([(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)] : List (Nat × Nat))) ∨ ((v.val,u.val) ∈ ([(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)] : List (Nat × Nat))), symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩, loopless := ⟨by intro v; fin_cases v <;> decide⟩ }
