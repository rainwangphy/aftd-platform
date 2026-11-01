import AFTD.Prelude

/-!
# efx_three_pair_anchor_start

Topic: fair_division   Node: 116b2b8dfb19

Provenance: helper lemma. Common-anchor lift of the OP-7 all-source three-split barrier; experiment 11720 and an unproved anchor-count projection.

The old pairs remain assigned to their owners, charity 8 is unallocated, and each agent receives r common anchors.
-/

def efx_three_pair_anchor_start (r : ℕ) (g : Fin (9 + 4*r)) : Fin 5 := if h : g.val < 9 then ![(0 : Fin 5),0,1,1,2,2,3,3,4] ⟨g.val, h⟩ else ⟨(g.val-9)%4, by omega⟩
