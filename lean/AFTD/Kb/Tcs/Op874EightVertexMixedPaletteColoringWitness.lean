import AFTD.Prelude

/-!
# op874_eight_vertex_mixed_palette_coloring_witness

Topic: graphs   Node: c6dc5ef8ebd7

Provenance: helper lemma. Positive local-state witness for the OP-874 matching-palette obstruction; https://arxiv.org/abs/2610.41950.

The displayed local states give a strong two-versus-four coloring with exact matching ownership on the eight-vertex all-matchings obstruction graph. Its factor is two four-cycles, so the separate four-window requirement is vacuous for that factor.
-/

theorem op874_eight_vertex_mixed_palette_coloring_witness :
    let L : Fin 12 → Fin 8 := ![0,0,0,1,1,2,2,3,4,4,5,6]
    let R : Fin 12 → Fin 8 := ![1,3,7,2,5,3,6,4,5,7,6,7]
    let inc : Fin 8 → Fin 3 → Fin 12 := ![![0,1,2],![0,3,4],![3,5,6],![1,5,7],![7,8,9],![4,8,10],![6,10,11],![2,9,11]]
    let M : Finset (Fin 12) := {2,4,6,7}
    let bit : Fin 8 → Bool := ![false,true,false,true,true,true,false,false]
    let c : Fin 12 → Fin 6 := ![5,2,0,3,1,4,0,1,3,4,2,5]
    let h : Fin 8 → Fin 3 → Fin 6 := ![![4,1,3],![0,2,4],![2,5,1],![3,5,0],![5,0,2],![0,5,4],![3,4,1],![1,2,3]]
    (∀ v i j, i ≠ j → c (inc v i) ≠ c (inc v j) ∧ h v i ≠ h v j) ∧
    (∀ v i j, h v i ≠ c (inc v j)) ∧
    (∀ e i j, inc (L e) i ≠ e → inc (R e) j ≠ e → h (L e) i ≠ h (R e) j) ∧
    (∀ e ∈ M, bit (L e) = bit (R e) ∧ c e = if bit (L e) then 1 else 0) ∧
    (∀ e ∉ M, 2 ≤ (c e).val) ∧
    (∀ e ∈ M, ∀ i j, inc (L e) i = e → inc (R e) j = e →
      ¬ (h (L e) i = (if bit (L e) then 0 else 1) ∧
         h (R e) j = (if bit (R e) then 0 else 1))) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
