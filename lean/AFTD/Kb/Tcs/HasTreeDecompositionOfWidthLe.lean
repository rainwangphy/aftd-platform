import AFTD.Prelude

/-!
# has_tree_decomposition_of_width_le

Topic: proof_complexity   Node: a8e06e8b6e0b

A graph G has a tree decomposition of width at most w: a finite tree T and bags chi(t), subsets of the vertices of G, such that every vertex lies in some bag, both ends of every edge lie in a common bag, for every vertex v the nodes whose bags contain v induce a connected subtree, and every bag has at most w + 1 vertices.
-/

/-- G has a tree decomposition of width at most w. -/
def has_tree_decomposition_of_width_le {α : Type*} (G : SimpleGraph α) (w : ℕ) : Prop :=
  ∃ (N : ℕ) (T : SimpleGraph (Fin N)) (χ : Fin N → Finset α),
    T.IsTree ∧
    (∀ v : α, ∃ t, v ∈ χ t) ∧
    (∀ u v : α, G.Adj u v → ∃ t, u ∈ χ t ∧ v ∈ χ t) ∧
    (∀ v : α, (T.induce {t | v ∈ χ t}).Connected) ∧
    (∀ t, (χ t).card ≤ w + 1)
