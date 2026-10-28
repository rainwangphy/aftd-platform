import AFTD.Prelude
import AFTD.Kb.Tcs.ExistsTriangleThroughThreePointsAvoiding
import AFTD.Kb.Tcs.SegmentsBlockPoints
import AFTD.Kb.Tcs.SegmentCrossingGraph
import AFTD.Kb.Tcs.NotCliqueFreeThreeOfCrossesCrossingPairTf
import AFTD.Kb.Tcs.SegmentCrossingOfMemOpenSegments

/-!
# blocking_card_three_of_three_crossing_points

Topic: combinatorics   Node: 5edc2f25d322

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover_of_le_three

If A, B, C are three pairwise distinct points of the plane, each lying in the relative interiors of the two segments of one of three distinct crossing pairs of a triangle-free family L (with each pair's two segments distinct), then L blocks some three-element point set.
-/

private lemma blocking_card_three_of_three_crossing_points_pair_cases
    (p₁ p₂ p₃ u v : ℝ × ℝ)
    (hu : u ∈ ({p₁, p₂, p₃} : Finset (ℝ × ℝ)))
    (hv : v ∈ ({p₁, p₂, p₃} : Finset (ℝ × ℝ)))
    (huv : u ≠ v) :
    s(u, v) = s(p₁, p₂) ∨ s(u, v) = s(p₂, p₃) ∨ s(u, v) = s(p₃, p₁) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> simp_all

private lemma blocking_card_three_of_three_crossing_points_step
    (L : Finset (Sym2 (ℝ × ℝ)))
    (h_tf : (segment_crossing_graph L).CliqueFree 3)
    (u v g₁ g₂ h₁ h₂ D p q : ℝ × ℝ)
    (hnotin : s(p, q) ∉ L)
    (heq : s(u, v) = s(p, q))
    (hDp : D ∈ openSegment ℝ p q)
    (hg : s(g₁, g₂) ∈ L) (hh : s(h₁, h₂) ∈ L) (hgh : s(g₁, g₂) ≠ s(h₁, h₂))
    (hDg : D ∈ openSegment ℝ g₁ g₂) (hDh : D ∈ openSegment ℝ h₁ h₂) :
    ¬ (segment_crossing_graph (insert s(u, v) L)).CliqueFree 3 := by
  have hDuv : D ∈ openSegment ℝ u v := by
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hDp
    · rwa [openSegment_symm]
  have hne1 : s(u, v) ≠ s(g₁, g₂) := by
    intro h
    apply hnotin
    rw [← heq, h]
    exact hg
  have hne2 : s(u, v) ≠ s(h₁, h₂) := by
    intro h
    apply hnotin
    rw [← heq, h]
    exact hh
  exact not_cliqueFree_three_of_crosses_crossing_pair_tf L h_tf
    (s(g₁, g₂)) (s(h₁, h₂)) hg hh hgh
    (segment_crossing_of_mem_openSegments g₁ g₂ h₁ h₂ D hDg hDh)
    u v hne1 hne2
    (segment_crossing_of_mem_openSegments u v g₁ g₂ D hDuv hDg)
    (segment_crossing_of_mem_openSegments u v h₁ h₂ D hDuv hDh)

/-- Three distinct interior crossing points of a triangle-free family yield a blocked 3-point set (sides of a triangle through A, B, C). -/
theorem blocking_card_three_of_three_crossing_points
    (L : Finset (Sym2 (ℝ × ℝ)))
    (h_tf : (segment_crossing_graph L).CliqueFree 3)
    (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ A B C : ℝ × ℝ)
    (ha : s(a₁, a₂) ∈ L) (hb : s(b₁, b₂) ∈ L) (hc : s(c₁, c₂) ∈ L)
    (hd : s(d₁, d₂) ∈ L) (he : s(e₁, e₂) ∈ L) (hf : s(f₁, f₂) ∈ L)
    (hab : s(a₁, a₂) ≠ s(b₁, b₂)) (hcd : s(c₁, c₂) ≠ s(d₁, d₂))
    (hef : s(e₁, e₂) ≠ s(f₁, f₂))
    (hA₁ : A ∈ openSegment ℝ a₁ a₂) (hA₂ : A ∈ openSegment ℝ b₁ b₂)
    (hB₁ : B ∈ openSegment ℝ c₁ c₂) (hB₂ : B ∈ openSegment ℝ d₁ d₂)
    (hC₁ : C ∈ openSegment ℝ e₁ e₂) (hC₂ : C ∈ openSegment ℝ f₁ f₂)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    ∃ P : Finset (ℝ × ℝ), segments_block_points L P ∧ P.card = 3 := by
  classical
  obtain ⟨p₁, p₂, p₃, h12, h23, h31, hAp12, hBp23, hCp31, hn12, hn23, hn31⟩ :=
    exists_triangle_through_three_points_avoiding A B C hAB hBC hCA L
  refine ⟨{p₁, p₂, p₃}, ?_, ?_⟩
  · intro u v hu hv huv
    rcases blocking_card_three_of_three_crossing_points_pair_cases p₁ p₂ p₃ u v hu hv huv
      with h | h | h
    · exact blocking_card_three_of_three_crossing_points_step L h_tf u v
        a₁ a₂ b₁ b₂ A p₁ p₂ hn12 h hAp12 ha hb hab hA₁ hA₂
    · exact blocking_card_three_of_three_crossing_points_step L h_tf u v
        c₁ c₂ d₁ d₂ B p₂ p₃ hn23 h hBp23 hc hd hcd hB₁ hB₂
    · exact blocking_card_three_of_three_crossing_points_step L h_tf u v
        e₁ e₂ f₁ f₂ C p₃ p₁ hn31 h hCp31 he hf hef hC₁ hC₂
  · simp [h12, h23, Ne.symm h31]
