import AFTD.Prelude

/-!
# op874_two_four_forest_matching_colors

Topic: graphs   Node: e0cb922255ee

Provenance: helper lemma. OP-874: two-versus-four forest and pair-degree obstruction, experiments 38473 and 38476.

The low colors of the 16-vertex obstruction occur exactly on the displayed perfect matching, and on each edge agree with the common matching-cut bit.
-/

theorem op874_two_four_forest_matching_colors :
    let L : Fin 24 → Fin 16 := ![0,0,0,1,1,2,2,3,3,4,4,5,6,6,6,7,8,9,10,11,11,12,13,14]
    let R : Fin 24 → Fin 16 := ![1,5,14,2,9,3,12,4,13,5,15,7,7,8,10,8,9,10,11,12,15,13,14,15]
    let color : Fin 24 → Fin 6 := ![4,2,1,2,0,4,1,5,0,3,1,0,2,1,3,5,4,5,0,5,4,2,3,5]
    let bits : Fin 16 → Bool := ![true,false,true,false,true,false,true,false,true,false,false,false,true,false,true,true]
    let indices : Finset (Fin 24) := {2,4,6,8,10,11,13,18}
    (∀ e, e ∈ indices ↔ color e = 0 ∨ color e = 1) ∧
    (∀ e ∈ indices, bits (L e) = bits (R e) ∧ color e = if bits (L e) then 1 else 0) := by decide
