import AFTD.Prelude

/-!
# petersen_ramsey_red_graph

Topic: graphs   Node: 53b3e7dfc289

Provenance: formalization of a published result. Source: arXiv:2611.09347 Section 3

The red graph G_R on 20 vertices, defined as the disjoint union of two complete graphs of order 9 and one complete graph of order 2.
-/

/-- The red graph on 20 vertices for the Petersen Ramsey lower bound, formed by the disjoint union of two copies of K_9 and one copy of K_2. -/
def petersen_ramsey_red_graph : SimpleGraph (Fin 20) := {
  Adj := fun u v => u ≠ v ∧ ((u.val < 9 ∧ v.val < 9) ∨ (9 ≤ u.val ∧ u.val < 18 ∧ 9 ≤ v.val ∧ v.val < 18) ∨ (18 ≤ u.val ∧ 18 ≤ v.val))
  symm := ⟨fun u v h => by
    rcases h with ⟨hne, h | h | h⟩
    · exact ⟨hne.symm, Or.inl ⟨h.2, h.1⟩⟩
    · exact ⟨hne.symm, Or.inr (Or.inl ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩)⟩
    · exact ⟨hne.symm, Or.inr (Or.inr ⟨h.2, h.1⟩)⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩
}
