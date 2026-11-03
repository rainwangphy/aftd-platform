import AFTD.Prelude

/-!
# bipartite_subset_graph

Topic: graphs   Node: 2f36ccbcbb19

Provenance: formalization of a published result. Source: arXiv:2610.42094, Definition 1.2

For integers k ≥ 2 and r ≥ 0, G(k,r) is the bipartite graph on two disjoint copies of the family of k-element subsets of {1, ..., 2k-1}, where two vertices a_S and b_T are adjacent if and only if |S ∩ T| ≤ r.
-/

/-- The bipartite subset graph G(k,r) whose two vertex classes are copies of the k-subsets of 2k-1, adjacent when their intersection has size at most r. -/
def bipartite_subset_graph (k r : ℕ) :
    SimpleGraph ({S : Finset (Fin (2 * k - 1)) // S.card = k} ⊕ {T : Finset (Fin (2 * k - 1)) // T.card = k}) := {
  Adj := fun
    | Sum.inl S, Sum.inr T => (S.1 ∩ T.1).card ≤ r
    | Sum.inr T, Sum.inl S => (S.1 ∩ T.1).card ≤ r
    | _, _ => False
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp at h ⊢ <;> exact h⟩
  loopless := ⟨by
    intro u
    cases u <;> simp⟩
}
