import AFTD.Prelude

/-!
# op309_girth7_seeded_twentyfour_graph

Topic: graphs   Node: 214bedfb4db6

Provenance: helper lemma. OP-309 terminal-seed obstruction, experiments 40452, 40454 and 40461.

The explicit cubic girth-seven twenty-four-vertex graph used for the fixed-forest terminal-seed obstruction.
-/

def op309_girth7_seeded_twentyfour_graph : SimpleGraph (Fin 24) := { Adj := fun u v => ((u.val,v.val) ∈ ([(0,1),(0,23),(0,12),(1,2),(1,8),(2,3),(2,19),(3,4),(3,15),(4,5),(4,11),(5,6),(5,22),(6,7),(6,18),(7,8),(7,14),(8,9),(9,10),(9,21),(10,11),(10,17),(11,12),(12,13),(13,14),(13,20),(14,15),(15,16),(16,17),(16,23),(17,18),(18,19),(19,20),(20,21),(21,22),(22,23)] : List (Nat × Nat))) ∨ ((v.val,u.val) ∈ ([(0,1),(0,23),(0,12),(1,2),(1,8),(2,3),(2,19),(3,4),(3,15),(4,5),(4,11),(5,6),(5,22),(6,7),(6,18),(7,8),(7,14),(8,9),(9,10),(9,21),(10,11),(10,17),(11,12),(12,13),(13,14),(13,20),(14,15),(15,16),(16,17),(16,23),(17,18),(18,19),(19,20),(20,21),(21,22),(22,23)] : List (Nat × Nat))), symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩, loopless := ⟨by intro v; fin_cases v <;> decide⟩ }
