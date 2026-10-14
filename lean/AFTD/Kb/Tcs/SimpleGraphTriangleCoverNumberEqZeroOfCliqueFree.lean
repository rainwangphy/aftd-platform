import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber

/-!
# simple_graph_triangle_cover_number_eq_zero_of_clique_free

Topic: graphs   Node: 079e47a1c627

Provenance: helper lemma. Sanity lemma for the triangle cover number, arXiv:2610.15539 (Tuza's conjecture under an edge-count condition).

A triangle-free graph has triangle cover number 0.
-/

theorem simple_graph_triangle_cover_number_eq_zero_of_clique_free {V : Type*}
    (G : SimpleGraph V) (h : G.CliqueFree 3) : simple_graph_triangle_cover_number G = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  exact ⟨∅, by simp, fun t ht => absurd ht (h t), rfl⟩
