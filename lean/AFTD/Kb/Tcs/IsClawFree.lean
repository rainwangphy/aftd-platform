import AFTD.Prelude

/-!
# IsClawFree

Topic: graphs   Node: dd4d4a114555

Provenance: formalization of a published result. Source: arXiv:2610.20129 Sec. 1.1

A simple graph G is claw-free if it does not contain the complete bipartite graph K_{1,3} as an induced subgraph.
-/

/-- A simple graph is claw-free if it does not contain K_{1,3} as an induced subgraph. -/
def IsClawFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ SimpleGraph.IsIndContained (completeBipartiteGraph (Fin 1) (Fin 3)) G
