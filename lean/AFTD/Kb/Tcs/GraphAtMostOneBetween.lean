import AFTD.Prelude

/-!
# graph_at_most_one_between

Topic: graphs   Node: 16c321090d83

Provenance: formalization of a published result. Source: arXiv:2610.39966 Lemma 3

In a connected graph G, if y lies between x and z and x lies between y and z, then x = y; hence among three distinct vertices, at most one lies between the other two.
-/

/-- At most one vertex lies between the other two among three distinct vertices in a connected graph. -/
theorem graph_at_most_one_between {V : Type*} (G : SimpleGraph V) (hconn : G.Connected)
    {x y z : V} (h1 : G.dist x y + G.dist y z = G.dist x z)
    (h2 : G.dist y x + G.dist x z = G.dist y z) : x = y := by
  have hsymm : G.dist y x = G.dist x y := SimpleGraph.dist_comm
  have hdist : G.dist x y = 0 := by omega
  exact hconn.dist_eq_zero_iff.mp hdist
