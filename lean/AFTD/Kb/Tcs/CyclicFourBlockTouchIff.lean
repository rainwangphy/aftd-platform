import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockEdge
import AFTD.Kb.Tcs.CyclicFourBlockTouch
import AFTD.Kb.Tcs.CyclicFourBlockSrc
import AFTD.Kb.Tcs.CyclicFourBlockDst

/-!
# cyclic_four_block_touch_iff

Topic: graphs   Node: 5019979525d4

Provenance: helper lemma. decomposition of cyclic_four_block_graph_exists_rich_neighbor_five_coloring

Step of cyclic_four_block_graph_exists_rich_neighbor_five_coloring: touch iff.
-/

theorem cyclic_four_block_touch_iff (m : ℕ) (e f : (Fin (2*m+5) × Fin 6)) :
    cyclic_four_block_touch m e f ↔ ∃ v, v ∈ cyclic_four_block_edge m e ∧ v ∈ cyclic_four_block_edge m f := by
  unfold cyclic_four_block_touch cyclic_four_block_edge
  simp only [Sym2.mem_iff]
  constructor
  · rintro (h|h|h|h)
    · exact ⟨_,Or.inl rfl,Or.inl (Fin.ext h)⟩
    · exact ⟨_,Or.inl rfl,Or.inr (Fin.ext h)⟩
    · exact ⟨_,Or.inr rfl,Or.inl (Fin.ext h)⟩
    · exact ⟨_,Or.inr rfl,Or.inr (Fin.ext h)⟩
  · rintro ⟨v,(he|he),(hf|hf)⟩
    · exact Or.inl (congrArg Fin.val (he.symm.trans hf))
    · exact Or.inr (Or.inl (congrArg Fin.val (he.symm.trans hf)))
    · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val (he.symm.trans hf))))
    · exact Or.inr (Or.inr (Or.inr (congrArg Fin.val (he.symm.trans hf))))
