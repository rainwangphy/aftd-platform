import AFTD.Prelude

/-!
# young_diagram_row_lens_sublist_embedding

Topic: combinatorics   Node: 1509a29a2742

Provenance: helper lemma. step towards latin_partition_is_wide

If the row-length list of ν is a sublist of that of μ, then the rows of ν sit inside distinct rows of μ of the same length: there is an injective map φ on row indices with μ.rowLen (φ k) = ν.rowLen k for every row k of ν.
-/

/-- A sublist of row lengths is realised by an injective choice of rows of the ambient diagram. -/
theorem young_diagram_row_lens_sublist_embedding (μ ν : YoungDiagram)
    (h : ν.rowLens.Sublist μ.rowLens) :
    ∃ φ : ℕ → ℕ, Function.Injective φ ∧ ∀ k, k < ν.colLen 0 → μ.rowLen (φ k) = ν.rowLen k := by
  rcases List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp h with ⟨f, hf⟩
  refine ⟨f, f.injective, fun k hk => ?_⟩
  have hk_len : k < ν.rowLens.length := by
    rw [ν.length_rowLens]
    exact hk
  have h1 : ν.rowLens[k]? = some (ν.rowLen k) := by
    rw [List.getElem?_eq_getElem hk_len, YoungDiagram.get_rowLens]
  have h2 : μ.rowLens[f k]? = some (ν.rowLen k) := by
    rw [← hf k, h1]
  rcases List.getElem?_eq_some_iff.mp h2 with ⟨hfk_len, h_elem⟩
  rw [YoungDiagram.get_rowLens] at h_elem
  exact h_elem
