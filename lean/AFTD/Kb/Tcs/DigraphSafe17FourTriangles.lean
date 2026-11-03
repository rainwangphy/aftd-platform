import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph

/-!
# digraph_safe17_four_triangles

Topic: graphs   Node: f17f5dc7f0cf

Provenance: helper lemma. Finite safe-cycle obstruction for OP-110; experiment 13260.

The displayed graph contains the four explicit directed triangles on vertices 0,1,4; 2,3,6; 5,7,9; and 8,10,12.
-/

private instance in504_safe17_decAdj_3 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

theorem digraph_safe17_four_triangles :
    digraph_safe17_graph.Adj 0 1 ∧ digraph_safe17_graph.Adj 1 4 ∧ digraph_safe17_graph.Adj 4 0 ∧
    digraph_safe17_graph.Adj 2 3 ∧ digraph_safe17_graph.Adj 3 6 ∧ digraph_safe17_graph.Adj 6 2 ∧
    digraph_safe17_graph.Adj 5 7 ∧ digraph_safe17_graph.Adj 7 9 ∧ digraph_safe17_graph.Adj 9 5 ∧
    digraph_safe17_graph.Adj 8 10 ∧ digraph_safe17_graph.Adj 10 12 ∧ digraph_safe17_graph.Adj 12 8 := by
  decide
