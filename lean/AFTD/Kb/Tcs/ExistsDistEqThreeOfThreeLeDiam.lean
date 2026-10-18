import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvatureLeTwoDivDist

/-!
# exists_dist_eq_three_of_three_le_diam

Topic: graphs   Node: e0dbbf6b1ffa

Provenance: helper lemma. step towards exists_dist_three_lly_curvature_le_cut

If the diameter of a finite connected graph is at least 3, then some pair of vertices is at distance exactly 3.
-/

/-- A finite graph whose diameter is at least 3 has a pair of vertices at distance exactly 3. -/
theorem exists_dist_eq_three_of_three_le_diam
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 ≤ G.diam) :
    ∃ x y : V, G.dist x y = 3 := by
  have hns : ¬ Subsingleton V := by
    intro hs
    have h0 : G.diam = 0 := SimpleGraph.diam_eq_zero.mpr (Or.inr hs)
    omega
  haveI : Nonempty V := by
    by_contra h
    exact hns ⟨fun a b => (h ⟨a⟩).elim⟩
  obtain ⟨u, v, huv⟩ := SimpleGraph.exists_dist_eq_diam (G := G)
  have h3 : 3 ≤ G.dist u v := by rw [huv]; exact hd
  have hne0 : G.dist u v ≠ 0 := by omega
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_dist_ne_zero hne0
  have hlen : 3 ≤ p.length := by rw [hp]; exact h3
  refine ⟨u, p.getVert 3, le_antisymm ?_ ?_⟩
  · have ht : (p.take 3).length = 3 := by
      rw [SimpleGraph.Walk.take_length]
      omega
    calc G.dist u (p.getVert 3) ≤ (p.take 3).length := SimpleGraph.dist_le _
      _ = 3 := ht
  · by_contra hcon
    have hcon2 : G.dist u (p.getVert 3) ≤ 2 := by omega
    have hdrop : G.dist (p.getVert 3) v ≤ (p.drop 3).length := SimpleGraph.dist_le _
    rw [SimpleGraph.Walk.drop_length] at hdrop
    have htri : G.dist u v ≤ G.dist u (p.getVert 3) + G.dist (p.getVert 3) v :=
      SimpleGraph.Reachable.dist_triangle_left (p.take 3).reachable v
    omega
