import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentCrossing
import AFTD.Kb.Tcs.SegmentCrossingSymm
import AFTD.Kb.Tcs.SegmentCrossingGraph

/-!
# vertex_cover_three_extracts_star_pairs

Topic: combinatorics   Node: fd5bee4fa63e

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover_of_le_three

If the crossing graph of a finite segment family has vertex cover number exactly 3, then one can extract three pairwise-distinct "cover" segments g₁,g₂,g₃ together with outside segments h₁,h₂,h₃, such that each hᵢ lies outside {g₁,g₂,g₃} and gᵢ crosses hᵢ — i.e. three crossing pairs attached to three distinct minimum-vertex-cover segments.
-/

/-- A minimum vertex cover of size 3 yields three star crossing pairs (gᵢ, hᵢ) with the gᵢ distinct and each hᵢ outside the cover. -/
theorem vertex_cover_three_extracts_star_pairs
    (L : Finset (Sym2 (ℝ × ℝ)))
    (h_vc : (segment_crossing_graph L).vertexCoverNum = 3) :
    ∃ (g1a g1b g2a g2b g3a g3b h1a h1b h2a h2b h3a h3b : ℝ × ℝ),
      s(g1a, g1b) ∈ L ∧ s(g2a, g2b) ∈ L ∧ s(g3a, g3b) ∈ L ∧
      s(h1a, h1b) ∈ L ∧ s(h2a, h2b) ∈ L ∧ s(h3a, h3b) ∈ L ∧
      s(g1a, g1b) ≠ s(g2a, g2b) ∧ s(g2a, g2b) ≠ s(g3a, g3b) ∧
      s(g1a, g1b) ≠ s(g3a, g3b) ∧
      s(h1a, h1b) ∉ ({s(g1a, g1b), s(g2a, g2b), s(g3a, g3b)} : Finset (Sym2 (ℝ × ℝ))) ∧
      s(h2a, h2b) ∉ ({s(g1a, g1b), s(g2a, g2b), s(g3a, g3b)} : Finset (Sym2 (ℝ × ℝ))) ∧
      s(h3a, h3b) ∉ ({s(g1a, g1b), s(g2a, g2b), s(g3a, g3b)} : Finset (Sym2 (ℝ × ℝ))) ∧
      segment_crossing s(g1a, g1b) s(h1a, h1b) ∧
      segment_crossing s(g2a, g2b) s(h2a, h2b) ∧
      segment_crossing s(g3a, g3b) s(h3a, h3b) := by
  classical
  set G := segment_crossing_graph L with hGdef
  have hvc : G.vertexCoverNum = 3 := by rw [hGdef]; exact h_vc
  obtain ⟨C, hCcard, hCcov⟩ := SimpleGraph.vertexCoverNum_exists G
  rw [hvc] at hCcard
  have hCfin : C.Finite := by
    rw [← Set.encard_lt_top_iff, hCcard]
    exact ENat.natCast_lt_top 3
  have key : ∀ g ∈ C, ∃ h : ↥L, G.Adj g h ∧ h ∉ C := by
    intro g hg
    by_contra hcon
    push Not at hcon
    have hcov' : G.IsVertexCover (C \ {g}) := by
      intro u v huv
      rcases hCcov huv with hu | hv
      · by_cases hug : u = g
        · subst hug
          exact Or.inr ⟨hcon v huv, by simp [huv.ne']⟩
        · exact Or.inl ⟨hu, by simp [hug]⟩
      · by_cases hvg : v = g
        · subst hvg
          exact Or.inl ⟨hcon u huv.symm, by simp [huv.ne]⟩
        · exact Or.inr ⟨hv, by simp [hvg]⟩
    have hle := SimpleGraph.IsVertexCover.vertexCoverNum_le hcov'
    rw [hvc] at hle
    have h2 : (C \ {g}).encard = 2 := by
      rw [Set.encard_sdiff_singleton_of_mem hg, hCcard]
      decide
    rw [h2] at hle
    exact absurd hle (by decide)
  have hCts_card : hCfin.toFinset.card = 3 := by
    have h := Set.Finite.encard_eq_coe_toFinset_card hCfin
    rw [hCcard] at h
    exact_mod_cast h.symm
  obtain ⟨g1, g2, g3, h12, h13, h23, hCts_eq⟩ := Finset.card_eq_three.mp hCts_card
  have hg1C : g1 ∈ C := by
    rw [← Set.Finite.mem_toFinset hCfin, hCts_eq]; simp
  have hg2C : g2 ∈ C := by
    rw [← Set.Finite.mem_toFinset hCfin, hCts_eq]; simp
  have hg3C : g3 ∈ C := by
    rw [← Set.Finite.mem_toFinset hCfin, hCts_eq]; simp
  obtain ⟨h1, hh1adj, hh1C⟩ := key g1 hg1C
  obtain ⟨h2, hh2adj, hh2C⟩ := key g2 hg2C
  obtain ⟨h3, hh3adj, hh3C⟩ := key g3 hg3C
  have split : ∀ e : Sym2 (ℝ × ℝ), ∃ a b : ℝ × ℝ, e = s(a, b) := by
    intro e
    exact Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
  obtain ⟨g1a, g1b, hg1e⟩ := split g1.val
  obtain ⟨g2a, g2b, hg2e⟩ := split g2.val
  obtain ⟨g3a, g3b, hg3e⟩ := split g3.val
  obtain ⟨h1a, h1b, hh1e⟩ := split h1.val
  obtain ⟨h2a, h2b, hh2e⟩ := split h2.val
  obtain ⟨h3a, h3b, hh3e⟩ := split h3.val
  have adj_cross : ∀ u v : ↥L, G.Adj u v → segment_crossing u.val v.val := by
    intro u v huv
    rw [hGdef] at huv
    simp only [segment_crossing_graph, SimpleGraph.fromRel] at huv
    rcases huv.2 with hc | hc
    · exact hc
    · exact (segment_crossing_symm _ _).mp hc
  have outside : ∀ h : ↥L, h ∉ C →
      h.val ∉ ({g1.val, g2.val, g3.val} : Finset (Sym2 (ℝ × ℝ))) := by
    intro h hh
    have hh' : h ∉ hCfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact hh
    rw [hCts_eq] at hh'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h1' => hh'.1 (Subtype.ext h1'), fun h2' => hh'.2.1 (Subtype.ext h2'),
      fun h3' => hh'.2.2 (Subtype.ext h3')⟩
  refine ⟨g1a, g1b, g2a, g2b, g3a, g3b, h1a, h1b, h2a, h2b, h3a, h3b,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hg1e]; exact g1.2
  · rw [← hg2e]; exact g2.2
  · rw [← hg3e]; exact g3.2
  · rw [← hh1e]; exact h1.2
  · rw [← hh2e]; exact h2.2
  · rw [← hh3e]; exact h3.2
  · rw [← hg1e, ← hg2e]; exact fun hh => h12 (Subtype.ext hh)
  · rw [← hg2e, ← hg3e]; exact fun hh => h23 (Subtype.ext hh)
  · rw [← hg1e, ← hg3e]; exact fun hh => h13 (Subtype.ext hh)
  · rw [← hh1e, ← hg1e, ← hg2e, ← hg3e]; exact outside h1 hh1C
  · rw [← hh2e, ← hg1e, ← hg2e, ← hg3e]; exact outside h2 hh2C
  · rw [← hh3e, ← hg1e, ← hg2e, ← hg3e]; exact outside h3 hh3C
  · rw [← hg1e, ← hh1e]; exact adj_cross g1 h1 hh1adj
  · rw [← hg2e, ← hh2e]; exact adj_cross g2 h2 hh2adj
  · rw [← hg3e, ← hh3e]; exact adj_cross g3 h3 hh3adj
