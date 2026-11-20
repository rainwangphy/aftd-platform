import AFTD.Prelude
import AFTD.Kb.Tcs.IsClawFree
import AFTD.Kb.Tcs.IsClawFreeTripleNeighbors

/-!
# op309_clawfree_cubic_every_vertex_in_triangle

Topic: graphs   Node: ae976fea3880

Provenance: helper lemma. Elementary structural step in the claw-free cubic route to OP-309.

Every vertex of a finite claw-free cubic graph lies in a triangle.
-/

theorem op309_clawfree_cubic_every_vertex_in_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hclaw : IsClawFree G)
    (hdegree : ∀ v, G.degree v = 3) :
    ∀ v, ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b ∧ G.Adj a b := by
  intro v
  have h3 : (G.neighborFinset v).card = 3 := by rw [G.card_neighborFinset_eq_degree]; exact hdegree v
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ := Finset.card_eq_three.mp h3
  have ha : G.Adj v a := (G.mem_neighborFinset v a).mp (by rw [hN]; simp)
  have hb : G.Adj v b := (G.mem_neighborFinset v b).mp (by rw [hN]; simp)
  have hc : G.Adj v c := (G.mem_neighborFinset v c).mp (by rw [hN]; simp)
  rcases is_claw_free_triple_neighbors G hclaw v a b c ha hb hc hab hbc hac with h | h | h
  · exact ⟨a, b, hab, ha, hb, h⟩
  · exact ⟨a, c, hac, ha, hc, h⟩
  · exact ⟨b, c, hbc, hb, hc, h⟩
