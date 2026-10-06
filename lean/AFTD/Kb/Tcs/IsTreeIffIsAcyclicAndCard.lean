import AFTD.Prelude

/-!
# is_tree_iff_is_acyclic_and_card

Topic: graphs   Node: 2ec9a5b50c2d

Provenance: formalization of a published result. Source: Diestel, Graph Theory, Theorem 1.5.1

A simple graph G on a finite vertex type V is a tree if and only if G is acyclic and the number of edges plus 1 equals the number of vertices.
-/

/-- A finite graph is a tree if and only if it is acyclic and |E| + 1 = |V|. -/
theorem is_tree_iff_is_acyclic_and_card {V : Type*} [Finite V] (G : SimpleGraph V) :
    G.IsTree ↔ G.IsAcyclic ∧ Nat.card G.edgeSet + 1 = Nat.card V := by
  refine ⟨fun h ↦ ⟨h.isAcyclic, (SimpleGraph.isTree_iff_connected_and_card.mp h).2⟩, fun h ↦ ?_⟩
  cases isEmpty_or_nonempty V
  · exfalso
    have : Nat.card V = 0 := Nat.card_eq_zero.mpr (Or.inl ‹IsEmpty V›)
    omega
  · obtain ⟨F, hGF, -, hFTree⟩ :=
      SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic (le_top : G ≤ ⊤) h.1
    have hFcard : Nat.card F.edgeSet + 1 = Nat.card V :=
      (SimpleGraph.isTree_iff_connected_and_card.mp hFTree).2
    have hcard : Nat.card F.edgeSet ≤ Nat.card G.edgeSet := by omega
    have hsub : G.edgeSet ⊆ F.edgeSet := SimpleGraph.edgeSet_mono hGF
    have heq : G.edgeSet = F.edgeSet :=
      Set.Finite.eq_of_subset_of_card_le (Set.toFinite F.edgeSet) hsub hcard
    have : G = F := SimpleGraph.edgeSet_injective heq
    rw [this]
    exact hFTree
