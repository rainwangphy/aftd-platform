import AFTD.Prelude

/-!
# op309_three_arm_graph

Topic: graphs   Node: 3f86a80ba059

Provenance: helper lemma. A small path-selection obstruction for OP-309.

The seven-vertex tree with three arms of length two.
-/

def op309_three_arm_graph : SimpleGraph (Fin 7) where
  Adj u v := ((u.val, v.val) ∈ ([(0,1), (1,2), (0,3), (3,6), (0,4), (4,5)] : List (ℕ × ℕ))) ∨
    ((v.val, u.val) ∈ ([(0,1), (1,2), (0,3), (3,6), (0,4), (4,5)] : List (ℕ × ℕ)))
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro u; fin_cases u <;> decide⟩
