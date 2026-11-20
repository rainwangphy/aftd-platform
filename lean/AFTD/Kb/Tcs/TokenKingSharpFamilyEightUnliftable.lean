import AFTD.Prelude
import AFTD.Kb.Tcs.HasNonattackingKingLift
import AFTD.Kb.Tcs.TokenKingSharpFamily
import AFTD.Kb.Tcs.ToroidalKingGraph

/-!
# token_king_sharp_family_eight_unliftable

Topic: graphs   Node: 123005a87ea0

Provenance: helper lemma. arXiv:2611.22830

On the 8-cycle, the candidate sharp family token_king_sharp_family 8 has no nonattacking king lift: ¬ has_nonattacking_king_lift 8 (token_king_sharp_family 8).
-/

private lemma tkse_key (r : {s : Finset (Fin 8) // s.card = 2} → Fin 8)
    (hmem : ∀ e ∈ token_king_sharp_family 8, r e ∈ e.val)
    (hadj : ∀ e₁ ∈ token_king_sharp_family 8, ∀ e₂ ∈ token_king_sharp_family 8, e₁ ≠ e₂ →
      ¬ (toroidal_king_graph 8).Adj (r e₁, e₁.val.sum id) (r e₂, e₂.val.sum id)) : False := by
  have mA0 : (⟨{0,1}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨0, 1, rfl, Or.inr ⟨by decide, by decide⟩⟩
  have mA1 : (⟨{1,2}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨1, 2, rfl, Or.inr ⟨by decide, by decide⟩⟩
  have mA2 : (⟨{2,3}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨2, 3, rfl, Or.inr ⟨by decide, by decide⟩⟩
  have mA3 : (⟨{3,4}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨3, 4, rfl, Or.inr ⟨by decide, by decide⟩⟩
  have mA4 : (⟨{4,5}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨4, 5, rfl, Or.inr ⟨by decide, by decide⟩⟩
  have mA5 : (⟨{5,6}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨5, 6, rfl, Or.inr ⟨by decide, by decide⟩⟩
  have mA6 : (⟨{6,7}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨6, 7, rfl, Or.inr ⟨by decide, by decide⟩⟩
  have mA7 : (⟨{7,0}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨7, 0, rfl, Or.inr ⟨by decide, by decide⟩⟩
  have mB0 : (⟨{0,4}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨0, 4, rfl, Or.inl (by decide)⟩
  have mB1 : (⟨{1,5}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨1, 5, rfl, Or.inl (by decide)⟩
  have mB2 : (⟨{2,6}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨2, 6, rfl, Or.inl (by decide)⟩
  have mB3 : (⟨{3,7}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}) ∈ token_king_sharp_family 8 := by
    simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨3, 7, rfl, Or.inl (by decide)⟩
  have vA0 : r ⟨{0,1}, by decide⟩ = 0 ∨ r ⟨{0,1}, by decide⟩ = 1 := by have h := hmem _ mA0; simpa using h
  have vA1 : r ⟨{1,2}, by decide⟩ = 1 ∨ r ⟨{1,2}, by decide⟩ = 2 := by have h := hmem _ mA1; simpa using h
  have vA2 : r ⟨{2,3}, by decide⟩ = 2 ∨ r ⟨{2,3}, by decide⟩ = 3 := by have h := hmem _ mA2; simpa using h
  have vA3 : r ⟨{3,4}, by decide⟩ = 3 ∨ r ⟨{3,4}, by decide⟩ = 4 := by have h := hmem _ mA3; simpa using h
  have vA4 : r ⟨{4,5}, by decide⟩ = 4 ∨ r ⟨{4,5}, by decide⟩ = 5 := by have h := hmem _ mA4; simpa using h
  have vA5 : r ⟨{5,6}, by decide⟩ = 5 ∨ r ⟨{5,6}, by decide⟩ = 6 := by have h := hmem _ mA5; simpa using h
  have vA6 : r ⟨{6,7}, by decide⟩ = 6 ∨ r ⟨{6,7}, by decide⟩ = 7 := by have h := hmem _ mA6; simpa using h
  have vA7 : r ⟨{7,0}, by decide⟩ = 7 ∨ r ⟨{7,0}, by decide⟩ = 0 := by have h := hmem _ mA7; simpa using h
  have vB0 : r ⟨{0,4}, by decide⟩ = 0 ∨ r ⟨{0,4}, by decide⟩ = 4 := by have h := hmem _ mB0; simpa using h
  have vB1 : r ⟨{1,5}, by decide⟩ = 1 ∨ r ⟨{1,5}, by decide⟩ = 5 := by have h := hmem _ mB1; simpa using h
  have vB2 : r ⟨{2,6}, by decide⟩ = 2 ∨ r ⟨{2,6}, by decide⟩ = 6 := by have h := hmem _ mB2; simpa using h
  have vB3 : r ⟨{3,7}, by decide⟩ = 3 ∨ r ⟨{3,7}, by decide⟩ = 7 := by have h := hmem _ mB3; simpa using h
  have tA0 : (⟨{0,1}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (1 : Fin 8) := by decide
  have tA1 : (⟨{1,2}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (3 : Fin 8) := by decide
  have tA2 : (⟨{2,3}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (5 : Fin 8) := by decide
  have tA3 : (⟨{3,4}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (7 : Fin 8) := by decide
  have tA4 : (⟨{4,5}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (1 : Fin 8) := by decide
  have tA5 : (⟨{5,6}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (3 : Fin 8) := by decide
  have tA6 : (⟨{6,7}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (5 : Fin 8) := by decide
  have tA7 : (⟨{7,0}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (7 : Fin 8) := by decide
  have tB0 : (⟨{0,4}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (4 : Fin 8) := by decide
  have tB1 : (⟨{1,5}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (6 : Fin 8) := by decide
  have tB2 : (⟨{2,6}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (0 : Fin 8) := by decide
  have tB3 : (⟨{3,7}, by decide⟩ : {s : Finset (Fin 8) // s.card = 2}).val.sum id = (2 : Fin 8) := by decide
  have j02 : ¬ (toroidal_king_graph 8).Adj (r ⟨{0,1}, by decide⟩, (1 : Fin 8)) (r ⟨{2,6}, by decide⟩, (0 : Fin 8)) := by
    have h := hadj _ mA0 _ mB2 (by decide); simpa [tA0, tB2] using h
  have j03 : ¬ (toroidal_king_graph 8).Adj (r ⟨{0,1}, by decide⟩, (1 : Fin 8)) (r ⟨{3,7}, by decide⟩, (2 : Fin 8)) := by
    have h := hadj _ mA0 _ mB3 (by decide); simpa [tA0, tB3] using h
  have j10 : ¬ (toroidal_king_graph 8).Adj (r ⟨{1,2}, by decide⟩, (3 : Fin 8)) (r ⟨{0,4}, by decide⟩, (4 : Fin 8)) := by
    have h := hadj _ mA1 _ mB0 (by decide); simpa [tA1, tB0] using h
  have j13 : ¬ (toroidal_king_graph 8).Adj (r ⟨{1,2}, by decide⟩, (3 : Fin 8)) (r ⟨{3,7}, by decide⟩, (2 : Fin 8)) := by
    have h := hadj _ mA1 _ mB3 (by decide); simpa [tA1, tB3] using h
  have j20 : ¬ (toroidal_king_graph 8).Adj (r ⟨{2,3}, by decide⟩, (5 : Fin 8)) (r ⟨{0,4}, by decide⟩, (4 : Fin 8)) := by
    have h := hadj _ mA2 _ mB0 (by decide); simpa [tA2, tB0] using h
  have j21 : ¬ (toroidal_king_graph 8).Adj (r ⟨{2,3}, by decide⟩, (5 : Fin 8)) (r ⟨{1,5}, by decide⟩, (6 : Fin 8)) := by
    have h := hadj _ mA2 _ mB1 (by decide); simpa [tA2, tB1] using h
  have j31 : ¬ (toroidal_king_graph 8).Adj (r ⟨{3,4}, by decide⟩, (7 : Fin 8)) (r ⟨{1,5}, by decide⟩, (6 : Fin 8)) := by
    have h := hadj _ mA3 _ mB1 (by decide); simpa [tA3, tB1] using h
  have j32 : ¬ (toroidal_king_graph 8).Adj (r ⟨{3,4}, by decide⟩, (7 : Fin 8)) (r ⟨{2,6}, by decide⟩, (0 : Fin 8)) := by
    have h := hadj _ mA3 _ mB2 (by decide); simpa [tA3, tB2] using h
  have j42 : ¬ (toroidal_king_graph 8).Adj (r ⟨{4,5}, by decide⟩, (1 : Fin 8)) (r ⟨{2,6}, by decide⟩, (0 : Fin 8)) := by
    have h := hadj _ mA4 _ mB2 (by decide); simpa [tA4, tB2] using h
  have j43 : ¬ (toroidal_king_graph 8).Adj (r ⟨{4,5}, by decide⟩, (1 : Fin 8)) (r ⟨{3,7}, by decide⟩, (2 : Fin 8)) := by
    have h := hadj _ mA4 _ mB3 (by decide); simpa [tA4, tB3] using h
  have j50 : ¬ (toroidal_king_graph 8).Adj (r ⟨{5,6}, by decide⟩, (3 : Fin 8)) (r ⟨{0,4}, by decide⟩, (4 : Fin 8)) := by
    have h := hadj _ mA5 _ mB0 (by decide); simpa [tA5, tB0] using h
  have j53 : ¬ (toroidal_king_graph 8).Adj (r ⟨{5,6}, by decide⟩, (3 : Fin 8)) (r ⟨{3,7}, by decide⟩, (2 : Fin 8)) := by
    have h := hadj _ mA5 _ mB3 (by decide); simpa [tA5, tB3] using h
  have j60 : ¬ (toroidal_king_graph 8).Adj (r ⟨{6,7}, by decide⟩, (5 : Fin 8)) (r ⟨{0,4}, by decide⟩, (4 : Fin 8)) := by
    have h := hadj _ mA6 _ mB0 (by decide); simpa [tA6, tB0] using h
  have j61 : ¬ (toroidal_king_graph 8).Adj (r ⟨{6,7}, by decide⟩, (5 : Fin 8)) (r ⟨{1,5}, by decide⟩, (6 : Fin 8)) := by
    have h := hadj _ mA6 _ mB1 (by decide); simpa [tA6, tB1] using h
  have j71 : ¬ (toroidal_king_graph 8).Adj (r ⟨{7,0}, by decide⟩, (7 : Fin 8)) (r ⟨{1,5}, by decide⟩, (6 : Fin 8)) := by
    have h := hadj _ mA7 _ mB1 (by decide); simpa [tA7, tB1] using h
  have j72 : ¬ (toroidal_king_graph 8).Adj (r ⟨{7,0}, by decide⟩, (7 : Fin 8)) (r ⟨{2,6}, by decide⟩, (0 : Fin 8)) := by
    have h := hadj _ mA7 _ mB2 (by decide); simpa [tA7, tB2] using h
  have D0 : r ⟨{2,6}, by decide⟩ = 6 ∨ r ⟨{3,7}, by decide⟩ = 3 := by
    rcases vA0 with hx | hx <;> rcases vB2 with h1 | h1 <;> rcases vB3 with h2 | h2 <;>
      simp only [hx, h1, h2] at j02 j03 ⊢ <;>
      first
        | decide
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j02
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j03
  have D1 : r ⟨{0,4}, by decide⟩ = 4 ∨ r ⟨{3,7}, by decide⟩ = 7 := by
    rcases vA1 with hx | hx <;> rcases vB0 with h1 | h1 <;> rcases vB3 with h2 | h2 <;>
      simp only [hx, h1, h2] at j10 j13 ⊢ <;>
      first
        | decide
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j10
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j13
  have D2 : r ⟨{0,4}, by decide⟩ = 0 ∨ r ⟨{1,5}, by decide⟩ = 5 := by
    rcases vA2 with hx | hx <;> rcases vB0 with h1 | h1 <;> rcases vB1 with h2 | h2 <;>
      simp only [hx, h1, h2] at j20 j21 ⊢ <;>
      first
        | decide
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j20
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j21
  have D3 : r ⟨{1,5}, by decide⟩ = 1 ∨ r ⟨{2,6}, by decide⟩ = 6 := by
    rcases vA3 with hx | hx <;> rcases vB1 with h1 | h1 <;> rcases vB2 with h2 | h2 <;>
      simp only [hx, h1, h2] at j31 j32 ⊢ <;>
      first
        | decide
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j31
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j32
  have D4 : r ⟨{2,6}, by decide⟩ = 2 ∨ r ⟨{3,7}, by decide⟩ = 7 := by
    rcases vA4 with hx | hx <;> rcases vB2 with h1 | h1 <;> rcases vB3 with h2 | h2 <;>
      simp only [hx, h1, h2] at j42 j43 ⊢ <;>
      first
        | decide
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j42
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j43
  have D5 : r ⟨{0,4}, by decide⟩ = 0 ∨ r ⟨{3,7}, by decide⟩ = 3 := by
    rcases vA5 with hx | hx <;> rcases vB0 with h1 | h1 <;> rcases vB3 with h2 | h2 <;>
      simp only [hx, h1, h2] at j50 j53 ⊢ <;>
      first
        | decide
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j50
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j53
  have D6 : r ⟨{0,4}, by decide⟩ = 4 ∨ r ⟨{1,5}, by decide⟩ = 1 := by
    rcases vA6 with hx | hx <;> rcases vB0 with h1 | h1 <;> rcases vB1 with h2 | h2 <;>
      simp only [hx, h1, h2] at j60 j61 ⊢ <;>
      first
        | decide
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j60
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j61
  have D7 : r ⟨{1,5}, by decide⟩ = 5 ∨ r ⟨{2,6}, by decide⟩ = 2 := by
    rcases vA7 with hx | hx <;> rcases vB1 with h1 | h1 <;> rcases vB2 with h2 | h2 <;>
      simp only [hx, h1, h2] at j71 j72 ⊢ <;>
      first
        | decide
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j71
        | exact absurd (by simp only [toroidal_king_graph, SimpleGraph.cycleGraph]; decide) j72
  rcases vB0 with h0 | h0 <;> rcases vB1 with h1 | h1 <;> rcases vB2 with h2 | h2 <;> rcases vB3 with h3 | h3 <;>
    simp only [h0, h1, h2, h3] at D0 D1 D2 D3 D4 D5 D6 D7 <;> simp_all

/-- On the 8-cycle, the candidate sharpness family is unliftable to nonattacking kings. -/
theorem token_king_sharp_family_eight_unliftable :
    ¬ has_nonattacking_king_lift 8 (token_king_sharp_family 8) := by
  intro h
  unfold has_nonattacking_king_lift at h
  obtain ⟨r, hmem, hadj⟩ := h
  exact tkse_key r hmem hadj
