import AFTD.Prelude
import AFTD.Kb.Tcs.IsClawFreeTripleNeighbors
import AFTD.Kb.Tcs.IsClawFree

/-!
# claw_free_adj_of_neighbors

Topic: graphs   Node: 6eb5104b70d2

Provenance: helper lemma. arXiv:2611.09072 Claw-free minimal factor-critical and bicritical graphs, Lemma 3.1

In any claw-free graph G, if a vertex x is adjacent to three pairwise distinct vertices u, v, and w, and w is adjacent to neither u nor v, then u and v are adjacent.
-/

/-- In a claw-free graph, if a vertex has three distinct neighbors and one is adjacent to neither of the other two, then the remaining two neighbors must be adjacent. -/
theorem claw_free_adj_of_neighbors {V : Type*} (G : SimpleGraph V) (hclaw : IsClawFree G)
    (x u v w : V) (hu : G.Adj x u) (hv : G.Adj x v) (hw : G.Adj x w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h_not_uw : ¬ G.Adj u w) (h_not_vw : ¬ G.Adj v w) :
    G.Adj u v := by
  have h := is_claw_free_triple_neighbors G hclaw x u v w hu hv hw huv hvw huw
  tauto
