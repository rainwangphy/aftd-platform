import AFTD.Prelude

/-!
# op309_k5_chord_cycle_graph

Topic: graphs   Node: 9730ac5423b9

Provenance: helper lemma. Finite obstruction to extending the chord-conflict construction of https://arxiv.org/abs/2611.24297 beyond outerplanar graphs; experiments 34597 and 34600.

The ten-cycle with additional matching edges 03, 15, 27, 48, 69.
-/

def op309_k5_chord_cycle_graph : SimpleGraph (Fin 10) where
  Adj u v := ((u.val, v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,9),(0,3),(1,5),(2,7),(4,8),(6,9)] : List (ℕ × ℕ))) ∨
    ((v.val, u.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,9),(0,3),(1,5),(2,7),(4,8),(6,9)] : List (ℕ × ℕ)))
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro u; fin_cases u <;> decide⟩
