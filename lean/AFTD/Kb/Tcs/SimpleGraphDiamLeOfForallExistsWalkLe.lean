import AFTD.Prelude

/-!
# simple_graph_diam_le_of_forall_exists_walk_le

Topic: graphs   Node: 77053df806e1

Provenance: helper lemma. Mathlib.Combinatorics.SimpleGraph.Diam

In any simple graph G on a type α, if for every pair of vertices u and v there exists a walk from u to v of length at most D, then the diameter of G is at most D.
-/

/-- If every pair of vertices in a simple graph has a walk of length at most D, the diameter is at most D. -/
theorem simple_graph_diam_le_of_forall_exists_walk_le
    {α : Type*} (G : SimpleGraph α) (D : ℕ)
    (h : ∀ u v : α, ∃ w : G.Walk u v, w.length ≤ D) :
    G.diam ≤ D := by
  apply ENat.toNat_le_of_le_natCast
  rw [G.ediam_le_iff]
  intro u v
  obtain ⟨w, hw⟩ := h u v
  exact w.edist_le.trans (Nat.cast_le.mpr hw)
