import AFTD.Prelude

/-!
# op874_eight_vertex_all_matching_contractions_four_colorable

Topic: graphs   Node: a5191c241334

Provenance: helper lemma. All-matching strong-local-state obstruction for OP-874; https://arxiv.org/abs/2610.41950.

For each perfect matching of the displayed eight-vertex cubic graph, its matching contraction admits a proper four-edge-coloring.
-/

theorem op874_eight_vertex_all_matching_contractions_four_colorable :
    let L : Fin 12 → Fin 8 := ![0,0,0,1,1,2,2,3,4,4,5,6]
    let R : Fin 12 → Fin 8 := ![1,3,7,2,5,3,6,4,5,7,6,7]
    let inc : Fin 8 → Fin 3 → Fin 12 := ![![0,1,2],![0,3,4],![3,5,6],![1,5,7],![7,8,9],![4,8,10],![6,10,11],![2,9,11]]
    ∀ M : Finset (Fin 12), (∀ v : Fin 8, (Finset.univ.filter fun i : Fin 3 => inc v i ∈ M).card = 1) →
    ∃ c : Fin 12 → Fin 4,
      (∀ v i j, i ≠ j → inc v i ∉ M → inc v j ∉ M → c (inc v i) ≠ c (inc v j)) ∧
      (∀ e ∈ M, ∀ i j, inc (L e) i ≠ e → inc (R e) j ≠ e →
        c (inc (L e) i) ≠ c (inc (R e) j)) := by
  dsimp only
  intro M hM
  have hmem : M ∈ ({ {2,4,6,7}, {1,4,6,9}, {2,3,7,10}, {1,3,9,10}, {0,5,9,10}, {1,3,8,11}, {0,5,8,11} } : Finset (Finset (Fin 12))) := by
    revert M hM
    set_option maxRecDepth 100000 in decide
  have hcases : M = {2,4,6,7} ∨ M = {1,4,6,9} ∨ M = {2,3,7,10} ∨ M = {1,3,9,10} ∨ M = {0,5,9,10} ∨ M = {1,3,8,11} ∨ M = {0,5,8,11} := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, or_assoc] using hmem
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨![0, 1, 0, 1, 0, 0, 0, 0, 2, 3, 3, 2], by
      set_option maxRecDepth 100000 in decide⟩
  · exact ⟨![0, 0, 1, 1, 0, 2, 0, 3, 2, 0, 3, 0], by
      set_option maxRecDepth 100000 in decide⟩
  · exact ⟨![0, 1, 0, 0, 1, 2, 3, 0, 0, 3, 0, 2], by
      set_option maxRecDepth 100000 in decide⟩
  · exact ⟨![0, 0, 1, 0, 1, 2, 3, 3, 0, 0, 0, 2], by
      set_option maxRecDepth 100000 in decide⟩
  · exact ⟨![0, 0, 1, 2, 3, 0, 1, 3, 0, 0, 0, 2], by
      set_option maxRecDepth 100000 in decide⟩
  · exact ⟨![0, 0, 1, 0, 1, 2, 3, 3, 0, 0, 2, 0], by
      set_option maxRecDepth 100000 in decide⟩
  · exact ⟨![0, 0, 1, 2, 3, 0, 3, 1, 0, 0, 2, 0], by
      set_option maxRecDepth 100000 in decide⟩
