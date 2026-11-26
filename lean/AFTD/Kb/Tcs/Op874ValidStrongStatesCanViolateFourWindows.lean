import AFTD.Prelude

/-!
# op874_valid_strong_states_can_violate_four_windows

Topic: graphs   Node: a0f82fbc89e7

Provenance: helper lemma. Local-state construction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

The displayed alternating twelve-cycle with six matching chords admits the displayed compatible six-color local states and exact matching-port ownership, but four consecutive unselected factor edges have a six-edge window omitting one of the four high colors. The mate table is a fixed-point-free involution with no cycle-adjacent chords.
-/

theorem op874_valid_strong_states_can_violate_four_windows :
    let mate : Fin 12 → Fin 12 := ![10,9,6,11,8,7,2,5,4,1,0,3]
    let bit : Fin 12 → Bool := ![false,true,false,true,false,true,false,true,false,true,false,true]
    let w : Fin 12 → Fin 4 := ![1,2,0,1,2,0,3,1,3,2,3,0]
    let h : Fin 12 → Fin 3 → Fin 6 := ![![2,3,5],![0,3,4],![1,3,5],![3,2,4],![3,5,0],![3,1,4],![5,2,1],![4,0,2],![2,0,5],![4,1,0],![0,5,1],![1,4,2]]
    let selected := fun i : Fin 12 =>
      h i 1 = (if bit i then 4 else 5) ∨
      h (i+1) 0 = (if bit (i+1) then 4 else 5)
    (∀ v, mate (mate v) = v ∧ mate v ≠ v ∧ mate v ≠ v+1 ∧ mate v ≠ v-1 ∧ bit (mate v) = bit v) ∧
    (∀ v, bit v ≠ bit (v+1)) ∧
    (∀ v, w (v-1) ≠ w v) ∧
    (∀ v i j, i ≠ j → h v i ≠ h v j) ∧
    (∀ v i, h v i ≠ (if bit v then 5 else 4) ∧
      h v i ≠ Fin.castAdd 2 (w (v-1)) ∧ h v i ≠ Fin.castAdd 2 (w v)) ∧
    (∀ v i j, i ≠ 1 → j ≠ 0 → h v i ≠ h (v+1) j) ∧
    (∀ v i j, i ≠ 2 → j ≠ 2 → h v i ≠ h (mate v) j) ∧
    (∀ v, ¬ (h v 2 = (if bit v then 4 else 5) ∧
      h (mate v) 2 = (if bit (mate v) then 4 else 5))) ∧
    (∀ j : Fin 4, ¬ selected (Fin.ofNat 12 j.val)) ∧
    (∀ j : Fin 6, w (11 + Fin.ofNat 12 j.val) ≠ 3) := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
