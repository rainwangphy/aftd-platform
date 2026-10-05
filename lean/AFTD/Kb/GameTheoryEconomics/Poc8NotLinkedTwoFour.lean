import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAbLinked
import AFTD.Kb.GameTheoryEconomics.Poc8Graph
import AFTD.Kb.GameTheoryEconomics.Poc8NotConnectedOfCut
import AFTD.Kb.GameTheoryEconomics.Poc8Adj

/-!
# poc8_not_linked_two_four

Topic: fair_division   Node: 5b503a4b5fdd

G is not (2,4)-linked: for M1 = {0,1} and M2 = {2,5,6,7}, any S1 ⊇ M1 disjoint from S2 ⊇ M2 lies in {0,1,3,4}, and {0,4} is cut off from {1,3} there, so S1 is disconnected.
-/

theorem poc8_not_linked_two_four : ¬ is_ab_linked poc8_graph 2 4 := by
  intro h
  obtain ⟨S1, S2, hd, h1, h2, hc1, -⟩ := h {0, 1} {2, 5, 6, 7} (by decide) (by decide) (by decide)
  have h0 : (0 : Fin 8) ∈ S1 := h1 (by simp)
  have h1' : (1 : Fin 8) ∈ S1 := h1 (by simp)
  have hout : ∀ v ∈ S1, v ≠ 2 ∧ v ≠ 5 ∧ v ≠ 6 ∧ v ≠ 7 := by
    intro v hv
    have hv2 : v ∉ S2 := Set.disjoint_left.mp hd hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hv2 (h2 (by simp))
  have key : ∀ v w : Fin 8, (w = 0 ∨ w = 4) → poc8_adj w v = true →
      v = 2 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 0 ∨ v = 4 := by decide
  refine poc8_not_connected_of_cut poc8_graph S1 {w | w = 0 ∨ w = 4} 0 1 h0 (by simp) h1'
    (by simp) ?_ hc1
  intro v w hv hw hadj
  obtain ⟨n2, n5, n6, n7⟩ := hout v hv
  rcases key v w hw hadj with h | h | h | h | h | h
  · exact absurd h n2
  · exact absurd h n5
  · exact absurd h n6
  · exact absurd h n7
  · exact Or.inl h
  · exact Or.inr h
