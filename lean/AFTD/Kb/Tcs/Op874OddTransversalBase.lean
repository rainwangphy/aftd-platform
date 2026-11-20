import AFTD.Prelude
import AFTD.Kb.Tcs.Op874OddTransversalFactorEdges
import AFTD.Kb.Tcs.Op874OddTransversalMatching

/-!
# op874_odd_transversal_base

Topic: graphs   Node: ea36e93524a6

Provenance: helper lemma. Explicit one-sided nonadjacent-defect obstruction adapted from https://arxiv.org/html/2309.12150 section 2.2, experiment 35359.

The explicit forty-two-vertex graph formed by the factor and matching edges.
-/

def op874_odd_transversal_base : SimpleGraph (Fin 42) := SimpleGraph.fromEdgeSet (↑(op874_odd_transversal_factor_edges ∪ op874_odd_transversal_matching) : Set (Sym2 (Fin 42)))
