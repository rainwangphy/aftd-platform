import AFTD.Prelude

/-!
# op309_fourteen_incidence_graph

Topic: graphs   Node: 3e537f97ad4b

Provenance: helper lemma. Fourteen-vertex incidence graph testing the OP-309 palette-splitting route, experiments 34658, 34662, 34668 and 34675.

The fourteen-vertex cubic graph with the displayed incidence edge list.
-/

def op309_fourteen_incidence_graph : SimpleGraph (Fin 14) where
  Adj u v := ((u.val, v.val) ∈ ([(0,7), (0,8), (0,9), (1,7), (2,7), (3,8), (4,8), (5,9), (6,9), (1,10), (1,13), (3,10), (5,10), (4,13), (6,13), (2,11), (2,12), (4,11), (5,11), (3,12), (6,12)] : List (ℕ × ℕ))) ∨
    ((v.val, u.val) ∈ ([(0,7), (0,8), (0,9), (1,7), (2,7), (3,8), (4,8), (5,9), (6,9), (1,10), (1,13), (3,10), (5,10), (4,13), (6,13), (2,11), (2,12), (4,11), (5,11), (3,12), (6,12)] : List (ℕ × ℕ)))
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro u; fin_cases u <;> decide⟩
