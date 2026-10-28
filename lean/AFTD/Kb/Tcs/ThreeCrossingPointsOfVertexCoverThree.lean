import AFTD.Prelude
import AFTD.Kb.Tcs.VertexCoverThreeExtractsStarPairs
import AFTD.Kb.Tcs.CrossingPointsDistinctOfTriangleFree
import AFTD.Kb.Tcs.SegmentCrossingGraph
import AFTD.Kb.Tcs.SegmentCrossing

/-!
# three_crossing_points_of_vertex_cover_three

Topic: combinatorics   Node: fae779a99dd0

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover_of_le_three

If a finite segment family has a triangle-free crossing graph and vertex cover number exactly 3, then there are three pairwise distinct points, each lying in the relative interiors of the two segments of one of three distinct crossing pairs of the family.
-/

/-- Vertex cover number 3 plus triangle-freeness yields three distinct crossing points, each interior to two distinct segments of L. -/
theorem three_crossing_points_of_vertex_cover_three
    (L : Finset (Sym2 (ℝ × ℝ)))
    (h_tf : (segment_crossing_graph L).CliqueFree 3)
    (h_vc : (segment_crossing_graph L).vertexCoverNum = 3) :
    ∃ (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ A B C : ℝ × ℝ),
      s(a₁, a₂) ∈ L ∧ s(b₁, b₂) ∈ L ∧ s(c₁, c₂) ∈ L ∧
      s(d₁, d₂) ∈ L ∧ s(e₁, e₂) ∈ L ∧ s(f₁, f₂) ∈ L ∧
      s(a₁, a₂) ≠ s(b₁, b₂) ∧ s(c₁, c₂) ≠ s(d₁, d₂) ∧ s(e₁, e₂) ≠ s(f₁, f₂) ∧
      A ∈ openSegment ℝ a₁ a₂ ∧ A ∈ openSegment ℝ b₁ b₂ ∧
      B ∈ openSegment ℝ c₁ c₂ ∧ B ∈ openSegment ℝ d₁ d₂ ∧
      C ∈ openSegment ℝ e₁ e₂ ∧ C ∈ openSegment ℝ f₁ f₂ ∧
      A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  obtain ⟨g1a, g1b, g2a, g2b, g3a, g3b, h1a, h1b, h2a, h2b, h3a, h3b,
          hg1, hg2, hg3, hh1, hh2, hh3,
          hgg12, hgg23, hgg13, hh1out, hh2out, hh3out,
          hx1, hx2, hx3⟩ := vertex_cover_three_extracts_star_pairs L h_vc
  simp only [segment_crossing, Sym2.lift_mk, Set.Nonempty, Set.mem_inter_iff] at hx1 hx2 hx3
  obtain ⟨A, hA1, hA2⟩ := hx1
  obtain ⟨B, hB1, hB2⟩ := hx2
  obtain ⟨C, hC1, hC2⟩ := hx3
  have h_dist := crossing_points_distinct_of_triangle_free L h_tf
    g1a g1b g2a g2b g3a g3b h1a h1b h2a h2b h3a h3b A B C
    hg1 hg2 hg3 hh1 hh2 hh3 hgg12 hgg23 hgg13 hh1out hh2out hh3out
    hA1 hA2 hB1 hB2 hC1 hC2
  have hne1 : s(g1a, g1b) ≠ s(h1a, h1b) := by
    intro h; apply hh1out; simp [← h]
  have hne2 : s(g2a, g2b) ≠ s(h2a, h2b) := by
    intro h; apply hh2out; simp [← h]
  have hne3 : s(g3a, g3b) ≠ s(h3a, h3b) := by
    intro h; apply hh3out; simp [← h]
  refine ⟨g1a, g1b, h1a, h1b, g2a, g2b, h2a, h2b, g3a, g3b, h3a, h3b, A, B, C,
          hg1, hh1, hg2, hh2, hg3, hh3,
          hne1, hne2, hne3,
          hA1, hA2, hB1, hB2, hC1, hC2,
          h_dist.1, h_dist.2.1, h_dist.2.2.symm⟩
