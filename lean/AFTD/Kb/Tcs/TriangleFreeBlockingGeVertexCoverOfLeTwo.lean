import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentCrossingSymm
import AFTD.Kb.Tcs.TriangleFreeBlockingGeVertexCoverOfLeOne
import AFTD.Kb.Tcs.SegmentCrossing
import AFTD.Kb.Tcs.SegmentCrossingGraph
import AFTD.Kb.Tcs.SegmentsBlockPoints

/-!
# triangle_free_blocking_ge_vertex_cover_of_le_two

Topic: combinatorics   Node: 02a51e816e64

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover

For every finite family of line segments L whose crossing graph is triangle-free and has vertex cover number at most 2, there exists a point set P blocked by L with cardinality at least the vertex cover number.
-/

/-- The triangle-free blocking lower bound holds when the crossing graph is triangle-free and has vertex cover number at most 2. -/
theorem triangle_free_blocking_ge_vertex_cover_of_le_two
    (L : Finset (Sym2 (ℝ × ℝ)))
    (h_tf : (segment_crossing_graph L).CliqueFree 3)
    (h_vc : (segment_crossing_graph L).vertexCoverNum ≤ 2) :
    ∃ P : Finset (ℝ × ℝ), segments_block_points L P ∧
      (segment_crossing_graph L).vertexCoverNum ≤ P.card := by
  by_cases h_le1 : (segment_crossing_graph L).vertexCoverNum ≤ 1
  · exact triangle_free_blocking_ge_vertex_cover_of_le_one L h_le1
  · have h_edge : ∃ (s₁ s₂ : L), (segment_crossing_graph L).Adj s₁ s₂ := by
      by_contra! h_no_edge
      have h_bot : segment_crossing_graph L = ⊥ := by
        ext u v
        simp [h_no_edge u v]
      have h_zero : (segment_crossing_graph L).vertexCoverNum = 0 := by
        rw [h_bot, SimpleGraph.vertexCoverNum_bot]
      exact h_le1 (by rw [h_zero]; exact bot_le)
    obtain ⟨s₁, s₂, hadj⟩ := h_edge
    have hcross12 : segment_crossing (s₁ : Sym2 (ℝ × ℝ)) (s₂ : Sym2 (ℝ × ℝ)) := by
      dsimp [segment_crossing_graph, SimpleGraph.fromRel] at hadj
      cases hadj.2 with
      | inl h => exact h
      | inr h => rwa [segment_crossing_symm]
    obtain ⟨x, hxs1, hxs2⟩ := hcross12
    have hcross12_keep : segment_crossing (s₁ : Sym2 (ℝ × ℝ)) (s₂ : Sym2 (ℝ × ℝ)) := ⟨x, hxs1, hxs2⟩
    let f : ℝ → Sym2 (ℝ × ℝ) := fun t => s((x.1 + t, x.2), (x.1 - t, x.2))
    have hinj : Set.InjOn f (Set.Ioi (0 : ℝ)) := by
      intro t₁ ht₁ t₂ ht₂ h
      change 0 < t₁ at ht₁
      change 0 < t₂ at ht₂
      dsimp [f] at h
      rw [Sym2.eq_iff] at h
      rcases h with (⟨h1, -⟩ | ⟨h1, -⟩)
      · have : (x.1 + t₁, x.2).1 = (x.1 + t₂, x.2).1 := congr_arg Prod.fst h1
        dsimp at this; linarith
      · have : (x.1 + t₁, x.2).1 = (x.1 - t₂, x.2).1 := congr_arg Prod.fst h1
        dsimp at this; linarith
    have hinf : (f '' Set.Ioi 0).Infinite := (Set.Ioi_infinite 0).image hinj
    obtain ⟨e, ⟨t, ht, rfl⟩, heL⟩ := hinf.exists_notMem_finite L.finite_toSet
    let u := (x.1 + t, x.2)
    let v := (x.1 - t, x.2)
    have huv : u ≠ v := by
      intro h
      change 0 < t at ht
      have h1 : (x.1 + t, x.2).1 = (x.1 - t, x.2).1 := congr_arg Prod.fst h
      dsimp at h1; linarith
    have hx_uv : x ∈ openSegment ℝ u v := by
      rw [openSegment_eq_image]
      refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      ext <;> dsimp <;> ring
    let P : Finset (ℝ × ℝ) := {u, v}
    have hP_card : P.card = 2 := Finset.card_pair huv
    refine ⟨P, ?_, by rw [hP_card]; exact h_vc⟩
    dsimp [segments_block_points]
    intro p q hp hq hpq
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hp hq
    have hpq_eq : s(p, q) = s(u, v) := by
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · contradiction
      · rfl
      · exact Sym2.eq_swap
      · contradiction
    rw [hpq_eq]
    intro hcf
    have hcross1 : segment_crossing s(u, v) (s₁ : Sym2 (ℝ × ℝ)) := ⟨x, hx_uv, hxs1⟩
    have hcross2 : segment_crossing s(u, v) (s₂ : Sym2 (ℝ × ℝ)) := ⟨x, hx_uv, hxs2⟩
    let L' := insert s(u, v) L
    let v0 : ↥L' := ⟨s(u, v), Finset.mem_insert_self _ _⟩
    let v1 : ↥L' := ⟨s₁.1, Finset.mem_insert_of_mem s₁.2⟩
    let v2 : ↥L' := ⟨s₂.1, Finset.mem_insert_of_mem s₂.2⟩
    have hv01 : v0 ≠ v1 := by
      intro h
      have : (v0 : Sym2 (ℝ × ℝ)) = (v1 : Sym2 (ℝ × ℝ)) := congr_arg (fun (w : ↥L') => (w : Sym2 (ℝ × ℝ))) h
      dsimp [v0, v1] at this
      have hs1in : (s₁ : Sym2 (ℝ × ℝ)) ∈ L := s₁.2
      rw [← this] at hs1in
      exact heL hs1in
    have hv02 : v0 ≠ v2 := by
      intro h
      have : (v0 : Sym2 (ℝ × ℝ)) = (v2 : Sym2 (ℝ × ℝ)) := congr_arg (fun (w : ↥L') => (w : Sym2 (ℝ × ℝ))) h
      dsimp [v0, v2] at this
      have hs2in : (s₂ : Sym2 (ℝ × ℝ)) ∈ L := s₂.2
      rw [← this] at hs2in
      exact heL hs2in
    have hv12 : v1 ≠ v2 := by
      intro h
      apply hadj.ne
      have hval : s₁.1 = s₂.1 := congr_arg (fun (w : ↥L') => (w : Sym2 (ℝ × ℝ))) h
      exact Subtype.ext hval
    have hadj01 : (segment_crossing_graph L').Adj v0 v1 := by
      dsimp [segment_crossing_graph, SimpleGraph.fromRel]
      refine ⟨hv01, Or.inl hcross1⟩
    have hadj02 : (segment_crossing_graph L').Adj v0 v2 := by
      dsimp [segment_crossing_graph, SimpleGraph.fromRel]
      refine ⟨hv02, Or.inl hcross2⟩
    have hadj12 : (segment_crossing_graph L').Adj v1 v2 := by
      dsimp [segment_crossing_graph, SimpleGraph.fromRel]
      refine ⟨hv12, Or.inl hcross12_keep⟩
    let S : Finset ↥L' := {v0, v1, v2}
    have hS_card : S.card = 3 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · intro h
        simp only [Finset.mem_singleton] at h
        exact hv12 h
      · intro h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact hv01 h
        · exact hv02 h
    have hS_clique : (segment_crossing_graph L').IsClique (S : Set ↥L') := by
      intro a ha b hb hab
      simp only [S, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · contradiction
      · exact hadj01
      · exact hadj02
      · exact hadj01.symm
      · contradiction
      · exact hadj12
      · exact hadj02.symm
      · exact hadj12.symm
      · contradiction
    have hnc : (segment_crossing_graph L').IsNClique 3 S := ⟨hS_clique, hS_card⟩
    exact hcf S hnc
