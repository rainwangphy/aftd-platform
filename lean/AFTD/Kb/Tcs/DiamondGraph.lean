import AFTD.Prelude

/-!
# diamond_graph

Topic: graphs   Node: 930dd32f5d89

Provenance: formalization of a published result. Source: arXiv:2610.32404:11

The diamond graph is the simple graph on vertex type Fin 4 obtained from the complete graph ⊤ by deleting the single edge between vertex 0 and vertex 3.
-/

/-- The diamond graph on vertex type Fin 4, obtained by deleting the edge between 0 and 3 from K_4. -/
def diamond_graph : SimpleGraph (Fin 4) := (⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 3)}
