import AFTD.Prelude

/-!
# op874_saturated_twenty_four_color_witness

Topic: graphs   Node: 7b59d1f38f87

Provenance: helper lemma. Finite coloring witness for the OP-874 campaign, https://arxiv.org/abs/2610.41950.

The displayed external and hidden colors give compatible six-color local states on the 24-vertex saturated-cut example, obey exact matching ownership and the four-window condition on its four factor cycles.
-/

theorem op874_saturated_twenty_four_color_witness :
    let L : Fin 36 → Fin 24 := ![0,0,0,1,1,2,2,3,3,4,5,5,5,6,7,7,8,8,10,10,10,11,12,13,14,16,16,16,17,17,18,18,19,20,21,22]
    let R : Fin 36 → Fin 24 := ![1,4,9,2,22,3,13,4,11,6,6,9,15,7,8,14,9,12,11,15,19,12,13,14,15,17,20,23,18,21,19,23,20,21,22,23]
    let inc : Fin 24 → Fin 3 → Fin 36 := ![![0,1,2],![0,3,4],![3,5,6],![5,7,8],![1,7,9],![10,11,12],![9,10,13],![13,14,15],![14,16,17],![2,11,16],![18,19,20],![8,18,21],![17,21,22],![6,22,23],![15,23,24],![12,19,24],![25,26,27],![25,28,29],![28,30,31],![20,30,32],![26,32,33],![29,33,34],![4,34,35],![27,31,35]]
    let h : Fin 24 → Fin 3 → Fin 6 := ![![3,1,2],![2,5,0],![0,4,5],![5,4,1],![2,1,4],![3,5,0],![1,3,4],![3,4,0],![4,1,5],![1,2,5],![3,0,2],![4,3,1],![1,3,5],![0,3,2],![4,0,2],![5,2,0],![5,1,2],![1,5,4],![4,0,3],![0,4,2],![2,4,1],![1,4,3],![3,4,0],![2,0,3]]
    let color : Fin 36 → Fin 6 := ![4,5,0,3,1,2,1,3,0,0,2,4,1,5,2,1,3,0,5,4,1,2,4,5,3,3,0,4,2,0,5,1,3,5,2,5]
    let bit : Fin 24 → Bool := ![false,true,true,false,false,true,false,true,false,false,true,false,false,true,true,true,false,false,true,true,false,false,true,true]
    let M : Finset (Fin 36) := {9,2,29,17,26,8,12,15,31,20,6,4}
    let selected : Fin 36 → Prop := fun e =>
      (∃ i : Fin 3, inc (L e) i = e ∧ h (L e) i = if bit (L e) then 0 else 1) ∨
      (∃ i : Fin 3, inc (R e) i = e ∧ h (R e) i = if bit (R e) then 0 else 1)
    let w5 : (Fin 5 → Fin 36) → Prop := fun f => ∀ i : Fin 5,
      (∀ j : Fin 4, ¬ selected (f (i + Fin.ofNat 5 j.val))) →
      ∀ k : Fin 4, ∃ j : Fin 6, color (f (i - 1 + Fin.ofNat 5 j.val)) = ⟨k.val + 2, by omega⟩
    let w6 : (Fin 6 → Fin 36) → Prop := fun f => ∀ i : Fin 6,
      (∀ j : Fin 4, ¬ selected (f (i + Fin.ofNat 6 j.val))) →
      ∀ k : Fin 4, ∃ j : Fin 6, color (f (i - 1 + Fin.ofNat 6 j.val)) = ⟨k.val + 2, by omega⟩
    let w8 : (Fin 8 → Fin 36) → Prop := fun f => ∀ i : Fin 8,
      (∀ j : Fin 4, ¬ selected (f (i + Fin.ofNat 8 j.val))) →
      ∀ k : Fin 4, ∃ j : Fin 6, color (f (i - 1 + Fin.ofNat 8 j.val)) = ⟨k.val + 2, by omega⟩
    (∀ v : Fin 24, ∀ i j : Fin 3, i ≠ j → inc v i ≠ inc v j) ∧
    (∀ v : Fin 24, ∀ i : Fin 3, L (inc v i) = v ∨ R (inc v i) = v) ∧
    (∀ v : Fin 24, ∀ i j : Fin 3, i ≠ j → color (inc v i) ≠ color (inc v j) ∧ h v i ≠ h v j) ∧
    (∀ v : Fin 24, ∀ i j : Fin 3, h v i ≠ color (inc v j)) ∧
    (∀ e : Fin 36, ∀ i j : Fin 3, inc (L e) i ≠ e → inc (R e) j ≠ e → h (L e) i ≠ h (R e) j) ∧
    (∀ e : Fin 36, e ∈ M → color e = if bit (L e) then 1 else 0) ∧
    (∀ e : Fin 36, e ∉ M → 2 ≤ (color e).val) ∧
    (∀ e : Fin 36, e ∈ M → ∀ i j : Fin 3, inc (L e) i = e → inc (R e) j = e →
      ¬ (h (L e) i = (if bit (L e) then 0 else 1) ∧ h (R e) j = (if bit (R e) then 0 else 1))) ∧
    w5 ![0,3,5,7,1] ∧ w5 ![10,13,14,16,11] ∧
    w6 ![18,21,22,23,24,19] ∧ w8 ![25,28,30,32,33,34,35,27] := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide
