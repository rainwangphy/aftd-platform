import AFTD.Prelude

/-!
# tree_hitting_time_index

Topic: graphs   Node: 3495be63241d

Provenance: formalization of a published result. Source: arXiv:2611.34295 Sec. 1

For a simple graph G on a finite vertex type V, tree_hitting_time_index G is the integer defined as the sum over all unordered pairs e : Sym2 V of max (hit u v) (hit v u) for e = ⟦(u, v)⟧, where hit u v = (Fintype.card V - 1 : ℤ) * (G.dist u v : ℤ) + ∑ w : V, ((G.dist w v : ℤ) - (G.dist w u : ℤ)).
-/

/-- The hitting time index HT(T) of a finite graph G on vertex type V, matching the tree hitting time index when G is a tree. -/
noncomputable def tree_hitting_time_index {V : Type*} [Fintype V] (G : SimpleGraph V) : ℤ :=
  let hit : V → V → ℤ := fun u v =>
    (Fintype.card V - 1 : ℤ) * (G.dist u v : ℤ) + ∑ w : V, ((G.dist w v : ℤ) - (G.dist w u : ℤ))
  ∑ e : Sym2 V, Sym2.lift ⟨fun u v => max (hit u v) (hit v u), fun _ _ => max_comm _ _⟩ e
