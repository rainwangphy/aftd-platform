import AFTD.Prelude

/-!
# op874_disjoint_palette_cut_coloring_witness

Topic: graphs   Node: ddbe956e4d13

Provenance: helper lemma. Positive witness for the matching-palette counterexample to an OP-874 shortcut; https://arxiv.org/abs/2610.41950.

An explicit six-color local-state assignment on the eight-vertex obstruction is strong, has exact matching-port ownership, and satisfies the four-window property. This shows the disjoint-palette failure does not obstruct an unrestricted coloring of the same cut.
-/

theorem op874_disjoint_palette_cut_coloring_witness :
    let mate : Fin 8 → Fin 8 := ![6,4,7,5,1,3,0,2]
    let bit : Fin 8 → Bool := ![true,false,false,true,false,true,true,false]
    let w : Fin 8 → Fin 4 := ![1,3,0,1,0,2,3,2]
    let h : Fin 8 → Fin 3 → Fin 6 := ![![4,3,0],![0,5,2],![2,5,1],![2,3,4],![2,3,5],![1,4,3],![1,0,4],![1,0,5]]
    let selected := fun i : Fin 8 =>
      h i 1 = (if bit i then 4 else 5) ∨
      h (i+1) 0 = (if bit (i+1) then 4 else 5)
    (∀ v, w (v-1) ≠ w v) ∧
    (∀ v i j, i ≠ j → h v i ≠ h v j) ∧
    (∀ v i, h v i ≠ (if bit v then 5 else 4) ∧
      h v i ≠ Fin.castAdd 2 (w (v-1)) ∧ h v i ≠ Fin.castAdd 2 (w v)) ∧
    (∀ v i j, i ≠ 1 → j ≠ 0 → h v i ≠ h (v+1) j) ∧
    (∀ v i j, i ≠ 2 → j ≠ 2 → h v i ≠ h (mate v) j) ∧
    (∀ v, ¬ (h v 2 = (if bit v then 4 else 5) ∧
      h (mate v) 2 = (if bit (mate v) then 4 else 5))) ∧
    (∀ i, (∀ j : Fin 4, ¬ selected (i + Fin.ofNat 8 j.val)) →
      ∀ c : Fin 4, ∃ j : Fin 6, w (i - 1 + Fin.ofNat 8 j.val) = c) := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
