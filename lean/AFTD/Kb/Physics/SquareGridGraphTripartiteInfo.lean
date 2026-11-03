import AFTD.Prelude
import AFTD.Kb.Physics.TreeGraphStateTripartiteInfo

/-!
# square_grid_graph_tripartite_info

Topic: quantum_mechanics   Node: 4393f15376bb

Provenance: formalization of a published result. Source: arXiv:2511.19585 ("Monogamy of Mutual Information in Graph States")

For any natural number n and four-coloring c : Fin n × Fin n → Fin 4 of the vertices of the n-by-n square grid graph, square_grid_graph_tripartite_info n c is the tripartite information tree_graph_state_tripartite_info of the four parts defined by the color classes of c.
-/

/-- Tripartite information I3(A:B:C) of a four-coloring c on the n-by-n square grid graph state. -/
noncomputable def square_grid_graph_tripartite_info (n : ℕ) (c : Fin n × Fin n → Fin 4) : ℤ := letI : DecidableRel (SimpleGraph.pathGraph n □ SimpleGraph.pathGraph n).Adj := Classical.decRel _
  tree_graph_state_tripartite_info (SimpleGraph.pathGraph n □ SimpleGraph.pathGraph n)
    (Finset.univ.filter (fun v => c v = 0))
    (Finset.univ.filter (fun v => c v = 1))
    (Finset.univ.filter (fun v => c v = 2))
    (Finset.univ.filter (fun v => c v = 3))
