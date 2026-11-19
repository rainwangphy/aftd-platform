import AFTD.Prelude

/-!
# op_2037_sharp_eight_graph

Topic: combinatorics   Node: 62b20045678a

Provenance: helper lemma. step towards op_2037_eight_not_extremal

The 8-vertex graph K_1 ∨ (K_4 ⊔ K_3): vertex 7 is universal and the remaining vertices split into the clique {0,2,4,6} and the clique {1,3,5}, with no edges between them.
-/

/-- The candidate counterexample graph K_1 ∨ (K_4 ⊔ K_3) on Fin 8 (16 edges, vertex 7 universal). -/
def op_2037_sharp_eight_graph : SimpleGraph (Fin 8) where
  Adj u v := u ≠ v ∧ (u = 7 ∨ v = 7 ∨ (u.val % 2 = v.val % 2 ∧ u ≠ 7 ∧ v ≠ 7))
  symm := by
    refine ⟨fun u v h => ?_⟩
    obtain ⟨hne, h⟩ := h
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h1.symm, h3, h2⟩)
  loopless := by
    refine ⟨fun u h => ?_⟩
    exact h.1 rfl
