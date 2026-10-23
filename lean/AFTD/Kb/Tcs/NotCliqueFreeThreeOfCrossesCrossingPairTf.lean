import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentCrossing
import AFTD.Kb.Tcs.SegmentCrossingGraph

/-!
# not_cliqueFree_three_of_crosses_crossing_pair_tf

Topic: combinatorics   Node: e8bf3cc545c9

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover

If L is a triangle-free segment family and a new segment uv crosses both segments of a crossing pair in L (distinct from both), then inserting uv creates a triangle in the crossing graph.
-/

/-- If a segment uv crosses both members of a crossing pair in L, then inserting uv creates a triangle in the crossing graph. -/
theorem not_cliqueFree_three_of_crosses_crossing_pair_tf
    (L : Finset (Sym2 (ℝ × ℝ)))
    (_h_tf : (segment_crossing_graph L).CliqueFree 3)
    (s₁ s₂ : Sym2 (ℝ × ℝ))
    (hs₁ : s₁ ∈ L) (hs₂ : s₂ ∈ L) (hs₁₂ : s₁ ≠ s₂)
    (hcross₁₂ : segment_crossing s₁ s₂)
    (u v : ℝ × ℝ)
    (h_ne1 : s(u, v) ≠ s₁) (h_ne2 : s(u, v) ≠ s₂)
    (hcross_u1 : segment_crossing s(u, v) s₁)
    (hcross_u2 : segment_crossing s(u, v) s₂) :
    ¬ (segment_crossing_graph (insert s(u, v) L)).CliqueFree 3 := by
  classical
  let L' : Finset (Sym2 (ℝ × ℝ)) := insert s(u, v) L
  let x0 : L' := ⟨s(u, v), by simp [L']⟩
  let x1 : L' := ⟨s₁, by simp [L', hs₁]⟩
  let x2 : L' := ⟨s₂, by simp [L', hs₂]⟩
  have h01 : x0 ≠ x1 := by
    intro h
    exact h_ne1 (Subtype.ext_iff.mp h)
  have h02 : x0 ≠ x2 := by
    intro h
    exact h_ne2 (Subtype.ext_iff.mp h)
  have h12 : x1 ≠ x2 := by
    intro h
    exact hs₁₂ (Subtype.ext_iff.mp h)
  have hadj01 : (segment_crossing_graph L').Adj x0 x1 := by
    rw [segment_crossing_graph, SimpleGraph.fromRel_adj]
    exact ⟨h01, Or.inl hcross_u1⟩
  have hadj02 : (segment_crossing_graph L').Adj x0 x2 := by
    rw [segment_crossing_graph, SimpleGraph.fromRel_adj]
    exact ⟨h02, Or.inl hcross_u2⟩
  have hadj12 : (segment_crossing_graph L').Adj x1 x2 := by
    rw [segment_crossing_graph, SimpleGraph.fromRel_adj]
    exact ⟨h12, Or.inl hcross₁₂⟩
  let t : Finset L' := {x0, x1, x2}
  have hcard : t.card = 3 := by
    simp [t, h01, h02, h12]
  have hclique : (segment_crossing_graph L').IsClique (↑t : Set L') := by
    rw [SimpleGraph.isClique_iff]
    intro a ha b hb hab
    simp [t] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact hadj01 | exact hadj02 | exact hadj12 |
        exact hadj01.symm | exact hadj02.symm | exact hadj12.symm | contradiction
  have hnic : (segment_crossing_graph L').IsNClique 3 t := ⟨hclique, hcard⟩
  exact hnic.not_cliqueFree
