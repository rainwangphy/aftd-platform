import AFTD.Prelude

/-!
# efx_three_pair_anchor_witness

Topic: fair_division   Node: bb374d2daa39

Provenance: helper lemma. Common-anchor lift of the OP-7 all-source three-split barrier; experiment 11720 and an unproved anchor-count projection.

Lift the explicit nine-good EFX completion while keeping the anchors round-robin.
-/

def efx_three_pair_anchor_witness (r : ℕ) (g : Fin (9 + 4*r)) : Fin 4 := if h : g.val < 9 then ![(0 : Fin 4),0,1,3,2,0,1,2,3] ⟨g.val, h⟩ else ⟨(g.val-9)%4, Nat.mod_lt _ (by decide)⟩
