import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeTokenOddCycleMatchingBoundNegation
import AFTD.Kb.Tcs.HasCooperativeColoringPair

/-!
# cycleGraph_three_no_cooperative_coloring

Topic: combinatorics   Node: 69958bfbee6d

Provenance: formalization of a published result. Source: arXiv:2611.34299 Lemma 3.4

Two copies of the 3-cycle graph on three vertices admit no cooperative coloring.
-/

/-- Two copies of the 3-cycle on 3 vertices admit no cooperative coloring. -/
theorem cycleGraph_three_no_cooperative_coloring :
    ¬ has_cooperative_coloring_pair (SimpleGraph.cycleGraph 3) (SimpleGraph.cycleGraph 3) := by
  rintro ⟨I₁, I₂, h₁, h₂, hunion⟩
  have adj_all : ∀ a b : Fin 3, a ≠ b → (SimpleGraph.cycleGraph 3).Adj a b := by decide
  have hnot : ∀ (I : Set (Fin 3)), (SimpleGraph.cycleGraph 3).IsIndepSet I →
      ∀ a b : Fin 3, a ∈ I → b ∈ I → a ≠ b → False := by
    intro I hI a b ha hb hab
    exact (hI ha hb hab) (adj_all a b hab)
  have hmem : ∀ x : Fin 3, x ∈ I₁ ∪ I₂ := fun x => by
    rw [hunion]; exact Set.mem_univ x
  rcases (Set.mem_union _ _ _).mp (hmem 0) with h0 | h0
  · have h1 : (1 : Fin 3) ∉ I₁ := fun h => hnot I₁ h₁ 0 1 h0 h (by decide)
    have h2 : (2 : Fin 3) ∉ I₁ := fun h => hnot I₁ h₁ 0 2 h0 h (by decide)
    rcases (Set.mem_union _ _ _).mp (hmem 1) with h | h
    · exact h1 h
    rcases (Set.mem_union _ _ _).mp (hmem 2) with h' | h'
    · exact h2 h'
    · exact hnot I₂ h₂ 1 2 h h' (by decide)
  · have h1 : (1 : Fin 3) ∉ I₂ := fun h => hnot I₂ h₂ 0 1 h0 h (by decide)
    have h2 : (2 : Fin 3) ∉ I₂ := fun h => hnot I₂ h₂ 0 2 h0 h (by decide)
    rcases (Set.mem_union _ _ _).mp (hmem 1) with h | h
    · rcases (Set.mem_union _ _ _).mp (hmem 2) with h' | h'
      · exact hnot I₁ h₁ 1 2 h h' (by decide)
      · exact h2 h'
    · exact h1 h
