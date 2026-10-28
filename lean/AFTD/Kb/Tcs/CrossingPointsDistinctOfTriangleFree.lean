import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentCrossingGraph
import AFTD.Kb.Tcs.SegmentCrossingOfMemOpenSegments
import AFTD.Kb.Tcs.SegmentCrossing

/-!
# crossing_points_distinct_of_triangle_free

Topic: combinatorics   Node: e4151b7374fc

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover_of_le_three

If the crossing graph of L is triangle-free and A, B, C are interior intersection points of three star crossing pairs {gᵢ,hᵢ} (with the gᵢ pairwise distinct and each hᵢ outside {g₁,g₂,g₃}), then A, B, C are pairwise distinct.
-/

lemma crossing_points_distinct_of_triangle_free_aux
    (L : Finset (Sym2 (ℝ × ℝ)))
    (h_tf : (segment_crossing_graph L).CliqueFree 3)
    (ga gb g'a g'b ha hb x : ℝ × ℝ)
    (hg : s(ga, gb) ∈ L) (hg' : s(g'a, g'b) ∈ L) (hh : s(ha, hb) ∈ L)
    (hgg' : s(ga, gb) ≠ s(g'a, g'b))
    (hgh : s(ga, gb) ≠ s(ha, hb))
    (hg'h : s(g'a, g'b) ≠ s(ha, hb))
    (hxg : x ∈ openSegment ℝ ga gb)
    (hxg' : x ∈ openSegment ℝ g'a g'b)
    (hxh : x ∈ openSegment ℝ ha hb) : False := by
  classical
  let x0 : L := ⟨s(ga, gb), hg⟩
  let x1 : L := ⟨s(g'a, g'b), hg'⟩
  let x2 : L := ⟨s(ha, hb), hh⟩
  have h01 : x0 ≠ x1 := fun h => hgg' (Subtype.ext_iff.mp h)
  have h02 : x0 ≠ x2 := fun h => hgh (Subtype.ext_iff.mp h)
  have h12 : x1 ≠ x2 := fun h => hg'h (Subtype.ext_iff.mp h)
  have hcross01 : segment_crossing s(ga, gb) s(g'a, g'b) :=
    segment_crossing_of_mem_openSegments ga gb g'a g'b x hxg hxg'
  have hcross02 : segment_crossing s(ga, gb) s(ha, hb) :=
    segment_crossing_of_mem_openSegments ga gb ha hb x hxg hxh
  have hcross12 : segment_crossing s(g'a, g'b) s(ha, hb) :=
    segment_crossing_of_mem_openSegments g'a g'b ha hb x hxg' hxh
  have hadj01 : (segment_crossing_graph L).Adj x0 x1 := by
    rw [segment_crossing_graph, SimpleGraph.fromRel_adj]
    exact ⟨h01, Or.inl hcross01⟩
  have hadj02 : (segment_crossing_graph L).Adj x0 x2 := by
    rw [segment_crossing_graph, SimpleGraph.fromRel_adj]
    exact ⟨h02, Or.inl hcross02⟩
  have hadj12 : (segment_crossing_graph L).Adj x1 x2 := by
    rw [segment_crossing_graph, SimpleGraph.fromRel_adj]
    exact ⟨h12, Or.inl hcross12⟩
  let t : Finset L := {x0, x1, x2}
  have hcard : t.card = 3 := by
    simp [t, h01, h02, h12]
  have hclique : (segment_crossing_graph L).IsClique (↑t : Set L) := by
    rw [SimpleGraph.isClique_iff]
    intro a ha b hb hab
    simp only [t, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact hadj01 | exact hadj02 | exact hadj12 |
        exact hadj01.symm | exact hadj02.symm | exact hadj12.symm | contradiction
  have hnic : (segment_crossing_graph L).IsNClique 3 t := ⟨hclique, hcard⟩
  exact hnic.not_cliqueFree h_tf

/-- Triangle-freeness forces the three crossing points of three star crossing pairs to be pairwise distinct. -/
theorem crossing_points_distinct_of_triangle_free
    (L : Finset (Sym2 (ℝ × ℝ)))
    (h_tf : (segment_crossing_graph L).CliqueFree 3)
    (g1a g1b g2a g2b g3a g3b h1a h1b h2a h2b h3a h3b A B C : ℝ × ℝ)
    (hg1 : s(g1a, g1b) ∈ L) (hg2 : s(g2a, g2b) ∈ L) (hg3 : s(g3a, g3b) ∈ L)
    (hh1 : s(h1a, h1b) ∈ L) (hh2 : s(h2a, h2b) ∈ L) (hh3 : s(h3a, h3b) ∈ L)
    (hgg12 : s(g1a, g1b) ≠ s(g2a, g2b)) (hgg23 : s(g2a, g2b) ≠ s(g3a, g3b))
    (hgg13 : s(g1a, g1b) ≠ s(g3a, g3b))
    (hh1out : s(h1a, h1b) ∉ ({s(g1a, g1b), s(g2a, g2b), s(g3a, g3b)} : Finset (Sym2 (ℝ × ℝ))))
    (hh2out : s(h2a, h2b) ∉ ({s(g1a, g1b), s(g2a, g2b), s(g3a, g3b)} : Finset (Sym2 (ℝ × ℝ))))
    (hh3out : s(h3a, h3b) ∉ ({s(g1a, g1b), s(g2a, g2b), s(g3a, g3b)} : Finset (Sym2 (ℝ × ℝ))))
    (hA1 : A ∈ openSegment ℝ g1a g1b) (hA2 : A ∈ openSegment ℝ h1a h1b)
    (hB1 : B ∈ openSegment ℝ g2a g2b) (hB2 : B ∈ openSegment ℝ h2a h2b)
    (hC1 : C ∈ openSegment ℝ g3a g3b) (hC2 : C ∈ openSegment ℝ h3a h3b) :
    A ≠ B ∧ B ≠ C ∧ A ≠ C := by
  have _ := hh3
  have _ := hh3out
  have _ := hC2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh1out hh2out
  have hg1h1 : s(g1a, g1b) ≠ s(h1a, h1b) := Ne.symm hh1out.1
  have hg2h1 : s(g2a, g2b) ≠ s(h1a, h1b) := Ne.symm hh1out.2.1
  have hg3h1 : s(g3a, g3b) ≠ s(h1a, h1b) := Ne.symm hh1out.2.2
  have hg2h2 : s(g2a, g2b) ≠ s(h2a, h2b) := Ne.symm hh2out.2.1
  have hg3h2 : s(g3a, g3b) ≠ s(h2a, h2b) := Ne.symm hh2out.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro hAB
    subst hAB
    exact crossing_points_distinct_of_triangle_free_aux L h_tf
      g1a g1b g2a g2b h1a h1b A
      hg1 hg2 hh1 hgg12 hg1h1 hg2h1 hA1 hB1 hA2
  · intro hBC
    subst hBC
    exact crossing_points_distinct_of_triangle_free_aux L h_tf
      g2a g2b g3a g3b h2a h2b B
      hg2 hg3 hh2 hgg23 hg2h2 hg3h2 hB1 hC1 hB2
  · intro hAC
    subst hAC
    exact crossing_points_distinct_of_triangle_free_aux L h_tf
      g1a g1b g3a g3b h1a h1b A
      hg1 hg3 hh1 hgg13 hg1h1 hg3h1 hA1 hC1 hA2
