import AFTD.Prelude

/-!
# graph_collinear_middle_unique

Topic: graphs   Node: 62453f87cbb4

Provenance: formalization of a published result. Source: arXiv:2610.39966 Lemma 3

Among three pairwise distinct vertices x, y, z in a connected graph G, if y lies between x and z (i.e. d(x,y) + d(y,z) = d(x,z)), then x cannot lie between y and z (i.e. d(y,x) + d(x,z) ≠ d(y,z)).
-/

/-- In a connected graph, at most one of three pairwise distinct vertices lies between the other two (Lemma 3). -/
theorem graph_collinear_middle_unique {V : Type*} (G : SimpleGraph V) (hG : G.Connected)
    {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h1 : G.dist x y + G.dist y z = G.dist x z) :
    G.dist y x + G.dist x z ≠ G.dist y z := by
  intro h2
  rw [SimpleGraph.dist_comm (u := y) (v := x)] at h2
  have h3 : G.dist x y = 0 := by omega
  exact hxy (hG.dist_eq_zero_iff.mp h3)
