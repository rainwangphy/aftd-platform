import AFTD.Prelude
import AFTD.Kb.Tcs.Op2378PetersenEdges

/-!
# op_2378_petersen_graph

Topic: graphs   Node: afebd92d7789

Provenance: helper lemma. step towards op_2378_partial_r_two

The Petersen graph on Fin 10, the graph whose edge set is op_2378_petersen_edges.
-/

/-- The Petersen graph on Fin 10 as the graph with edge set `op_2378_petersen_edges`. -/
def op_2378_petersen_graph : SimpleGraph (Fin 10) := SimpleGraph.fromEdgeSet (↑op_2378_petersen_edges : Set (Sym2 (Fin 10)))
