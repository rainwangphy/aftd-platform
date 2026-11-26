import AFTD.Prelude

/-!
# op874_tight_cut_free_low_coloring_witness

Topic: graphs   Node: c7b659c02f32

Provenance: helper lemma. Positive witness for the tight-cut fixed-low obstruction in OP-874; https://arxiv.org/abs/2610.41950.

The displayed local states give an exact-owner strong two-versus-four coloring with the four-window property on the tight 1:2 matching-cut graph after changing the low-port selection.
-/

theorem op874_tight_cut_free_low_coloring_witness :
    let L : Fin 18 → Fin 12 := ![0,0,0,1,1,2,2,2,3,3,4,4,5,6,7,8,9,10]
    let R : Fin 18 → Fin 12 := ![1,7,8,10,11,3,5,9,4,6,5,6,10,7,8,9,11,11]
    let inc : Fin 12 → Fin 3 → Fin 18 := ![![0,1,2],![0,3,4],![5,6,7],![5,8,9],![8,10,11],![6,10,12],![9,11,13],![1,13,14],![2,14,15],![7,15,16],![3,12,17],![4,16,17]]
    let M : Finset (Fin 18) := {0,5,10,13,15,17}
    let bit : Fin 12 → Bool := ![false,false,false,false,true,true,true,true,true,true,true,true]
    let c : Fin 18 → Fin 6 := ![0,5,4,2,4,0,4,3,2,3,1,5,3,1,2,1,5,1]
    let h : Fin 12 → Fin 3 → Fin 6 := ![![1,2,3],![3,1,5],![1,5,2],![5,1,4],![4,3,0],![2,0,5],![2,4,0],![3,4,0],![5,3,0],![2,4,0],![5,0,4],![3,2,0]]
    let selected : Fin 18 → Prop := fun e =>
      (∃ i : Fin 3, inc (L e) i = e ∧ h (L e) i = if bit (L e) then 0 else 1) ∨
      (∃ i : Fin 3, inc (R e) i = e ∧ h (R e) i = if bit (R e) then 0 else 1)
    let cyc : Fin 6 → Fin 18 := ![3,12,6,7,16,4]
    (∀ v i j, i ≠ j → c (inc v i) ≠ c (inc v j) ∧ h v i ≠ h v j) ∧
    (∀ v i j, h v i ≠ c (inc v j)) ∧
    (∀ e i j, inc (L e) i ≠ e → inc (R e) j ≠ e → h (L e) i ≠ h (R e) j) ∧
    (∀ e ∈ M, bit (L e) = bit (R e) ∧ c e = if bit (L e) then 1 else 0) ∧
    (∀ e ∉ M, 2 ≤ (c e).val) ∧
    (∀ e ∈ M, ∀ i j, inc (L e) i = e → inc (R e) j = e →
      ¬ (h (L e) i = (if bit (L e) then 0 else 1) ∧
         h (R e) j = (if bit (R e) then 0 else 1))) ∧
    (∀ i : Fin 6, (∀ j : Fin 4, ¬ selected (cyc (i + Fin.ofNat 6 j.val))) →
      ∀ k : Fin 4, ∃ j : Fin 6, c (cyc (i - 1 + Fin.ofNat 6 j.val)) = ⟨k.val + 2, by omega⟩) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro i h_win
  fin_cases i
  · exfalso; apply h_win 0; exact Or.inl ⟨1, by decide⟩
  · exfalso; apply h_win 0; exact Or.inr ⟨1, by decide⟩
  · exfalso; apply h_win 2; exact Or.inl ⟨2, by decide⟩
  · exfalso; apply h_win 1; exact Or.inl ⟨2, by decide⟩
  · exfalso; apply h_win 0; exact Or.inl ⟨2, by decide⟩
  · exfalso; apply h_win 1; exact Or.inl ⟨1, by decide⟩
