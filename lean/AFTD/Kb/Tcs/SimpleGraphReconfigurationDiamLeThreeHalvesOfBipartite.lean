import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphDiamLeOfForallExistsWalkLe
import AFTD.Kb.Tcs.SimpleGraphReconfigurationExistsWalkLeThreeHalvesOfBipartite
import AFTD.Kb.Tcs.SimpleGraphReconfigurationGraph

/-!
# simple_graph_reconfiguration_diam_le_three_halves_of_bipartite

Topic: graphs   Node: 5ca2f7ccc084

Provenance: formalization of a published result. Source: arXiv:2611.17022 Lemma 6 -- Large diameter for (Δ+2)-colouring reconfiguration

Let G be a finite bipartite simple graph on a type V with decidable equality and decidable adjacency. For every integer k ≥ G.maxDegree + 2, the diameter of the k-colouring reconfiguration graph of G with colours in Fin k is at most 3 * Fintype.card V / 2.
-/

/-- Upper bound of ⌊3n/2⌋ on the recoloring diameter of a bipartite graph with k ≥ Δ(G) + 2 colours. -/
theorem simple_graph_reconfiguration_diam_le_three_halves_of_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsBipartite)
    {k : ℕ} (hk : G.maxDegree + 2 ≤ k) :
    (simple_graph_reconfiguration_graph G k).diam ≤ 3 * Fintype.card V / 2 := simple_graph_diam_le_of_forall_exists_walk_le _ _
  (simple_graph_reconfiguration_exists_walk_le_three_halves_of_bipartite G hG hk)
