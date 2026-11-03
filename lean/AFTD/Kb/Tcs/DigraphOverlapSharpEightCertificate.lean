import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOverlapSharpEightGraph

/-!
# digraph_overlap_sharp_eight_certificate

Topic: graphs   Node: 4e37e1978f71

Provenance: helper lemma. Finite witness that the dirty-parent plus missing-image-arc accounting can attain three times overlap in the OP-110 route; experiment 13163.

The displayed eight-vertex graph is loopless, oriented and arc-dominated; vertex 7 is a sink. Its only unordered pair of vertices with at least two common predecessors is 2 and 7, which has exactly three common predecessors, namely 0, 1 and 5.
-/

private instance in504_sharp_decAdj : DecidableRel digraph_overlap_sharp_eight_graph.Adj := by
  intro u v
  unfold digraph_overlap_sharp_eight_graph
  infer_instance

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem digraph_overlap_sharp_eight_certificate :
    (∀ u, ¬ digraph_overlap_sharp_eight_graph.Adj u u) ∧
    (∀ u v, digraph_overlap_sharp_eight_graph.Adj u v → ¬ digraph_overlap_sharp_eight_graph.Adj v u) ∧
    (∀ u v, digraph_overlap_sharp_eight_graph.Adj u v →
      ∃ p, digraph_overlap_sharp_eight_graph.Adj p u ∧ digraph_overlap_sharp_eight_graph.Adj p v) ∧
    (∀ v, ¬ digraph_overlap_sharp_eight_graph.Adj 7 v) ∧
    (∀ a b : Fin 8, a.val < b.val →
      (2 ≤ (Finset.univ.filter fun p =>
        digraph_overlap_sharp_eight_graph.Adj p a ∧ digraph_overlap_sharp_eight_graph.Adj p b).card ↔
        a = 2 ∧ b = 7)) ∧
    ((Finset.univ.filter fun p =>
      digraph_overlap_sharp_eight_graph.Adj p 2 ∧ digraph_overlap_sharp_eight_graph.Adj p 7).card = 3) ∧
    (∀ p ∈ ({0, 1, 5} : Finset (Fin 8)),
      digraph_overlap_sharp_eight_graph.Adj p 2 ∧ digraph_overlap_sharp_eight_graph.Adj p 7) := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  · decide
