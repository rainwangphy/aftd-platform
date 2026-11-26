import AFTD.Prelude

/-!
# op309_bridgeless_gap_twenty_graph

Topic: graphs   Node: 486ef4336230

Provenance: helper lemma. OP-309 bridgeless family, experiments 40822 and 40826.

The 20-vertex four-block motif for the bridgeless uncovered-deficit family.
-/

def op309_bridgeless_gap_twenty_graph : SimpleGraph (Fin 20) := { Adj := fun u v => ((u.val,v.val) ∈ ([(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,7),(3,12),(4,17),(5,7),(5,8),(5,9),(6,7),(6,8),(6,9),(8,13),(9,18),(10,12),(10,13),(10,14),(11,12),(11,13),(11,14),(14,19),(15,17),(15,18),(15,19),(16,17),(16,18),(16,19)] : List (Nat × Nat))) ∨ ((v.val,u.val) ∈ ([(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,7),(3,12),(4,17),(5,7),(5,8),(5,9),(6,7),(6,8),(6,9),(8,13),(9,18),(10,12),(10,13),(10,14),(11,12),(11,13),(11,14),(14,19),(15,17),(15,18),(15,19),(16,17),(16,18),(16,19)] : List (Nat × Nat))), symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩, loopless := ⟨by intro v; fin_cases v <;> decide⟩ }
