import AFTD.Prelude
import AFTD.Kb.Physics.BipartiteSubgraphMagicPoly
import AFTD.Kb.Physics.FortuinKasteleynPoly

/-!
# op_1695_bipartite_graph_fortuin_kasteleyn

Topic: quantum_mechanics   Node: 8541b52c0a9e

Provenance: formalization of a published result. Source: OP-1695

For every bipartite simple graph G = (V, E), the bipartite subgraph polynomial bipartite_subgraph_magic_poly G equals 8^{-|V|} times the Fortuin-Kasteleyn polynomial fortuin_kasteleyn_poly G 8 (-2).
-/

private lemma op_1695_bipartite_graph_fortuin_kasteleyn_from_edge_set_is_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsBipartite)
    (A : Finset (Sym2 V)) (hA : A ⊆ G.edgeFinset) :
    (SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))).IsBipartite := by
  obtain ⟨c⟩ := hG
  have hsub : (↑A : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mp (hA (Finset.mem_coe.mp he))
  have hle : SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V)) ≤ G := by
    rw [SimpleGraph.fromEdgeSet_le]
    exact fun e he => hsub he.1
  refine ⟨⟨c.toFun, ?_⟩⟩
  intro a b hadj
  exact c.map_rel' (hle hadj)

/-- For a bipartite graph, the bipartite subgraph magic polynomial equals 8^{-|V|} Z_G(8, -2). -/
theorem op_1695_bipartite_graph_fortuin_kasteleyn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsBipartite) :
    bipartite_subgraph_magic_poly G = (1 / (8 ^ Fintype.card V : ℝ)) * fortuin_kasteleyn_poly G 8 (-2) := by
  rw [bipartite_subgraph_magic_poly, fortuin_kasteleyn_poly]
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  rw [if_pos (op_1695_bipartite_graph_fortuin_kasteleyn_from_edge_set_is_bipartite G hG A (Finset.mem_powerset.mp hA))]
