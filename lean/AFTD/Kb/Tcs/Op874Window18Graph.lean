import AFTD.Prelude
import AFTD.Kb.Tcs.Op874Window18Edges

/-!
# op874_window18_graph

Topic: graphs   Node: 0a0b7f399df6

Provenance: helper lemma. Eighteen-vertex fixed-cut four-window obstruction for the OP-874 campaign.

The simple cubic base graph of the fixed-cut window obstruction.
-/

def op874_window18_graph : SimpleGraph (Fin 18) := SimpleGraph.fromEdgeSet (↑op874_window18_edges : Set (Sym2 (Fin 18)))
