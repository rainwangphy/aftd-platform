import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FourteenRunEdges

/-!
# op874_fourteen_run_graph

Topic: graphs   Node: 108f7645f6cb

Provenance: helper lemma. All-matching maximum-cut palette obstruction for OP-874, using the local criterion in https://arxiv.org/abs/2610.41950.

The finite cubic graph used for the all-matching maximum-cut run obstruction.
-/

def op874_fourteen_run_graph : SimpleGraph (Fin 14) := SimpleGraph.fromEdgeSet (↑op874_fourteen_run_edges : Set (Sym2 (Fin 14)))
