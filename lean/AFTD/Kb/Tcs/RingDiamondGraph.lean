import AFTD.Prelude
import AFTD.Kb.Tcs.RingDiamondEdgeFinset

/-!
# ring_diamond_graph

Topic: combinatorics   Node: 345ed0422e03

Provenance: helper lemma. step towards near_minimum_cycle_counting_bound_real_exponent

The ring of 20 diamonds: the simple graph on the vertices (i,c) with i < 20 and c < 3 whose edge set is `ring_diamond_edge_finset`, i.e. 20 blocks, each joining the ring vertices (i,0) and (i+1,0) (indices mod 20) by two internally disjoint paths of length 2.
-/

open Sym2 in
/-- The ring of 20 diamonds: the simple graph on the 60 vertices (i,c) whose edges are the 80 edges of `ring_diamond_edge_finset`. -/
def ring_diamond_graph : SimpleGraph (Fin 20 × Fin 3) := SimpleGraph.fromEdgeSet (↑ring_diamond_edge_finset : Set (Sym2 (Fin 20 × Fin 3)))
