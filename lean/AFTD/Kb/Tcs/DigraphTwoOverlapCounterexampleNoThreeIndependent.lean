import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphTwoOverlapCounterexampleGraph

/-!
# digraph_two_overlap_counterexample_no_three_independent

Topic: graphs   Node: 5616a7da13e1

Provenance: helper lemma. Finite verification of the auxiliary independence obstruction to the 2z good-center route for OP-110; experiment 13207.

In the displayed thirteen-vertex counterexample, among any three distinct vertices some pair has a common predecessor; equivalently the auxiliary graph has independence number at most two.
-/

private instance in504_independence_decAdj : DecidableRel digraph_two_overlap_counterexample_graph.Adj := by
  intro u v
  unfold digraph_two_overlap_counterexample_graph
  infer_instance

theorem digraph_two_overlap_counterexample_no_three_independent :
    ∀ a b c : Fin 13, a ≠ b → a ≠ c → b ≠ c →
      (∃ p, digraph_two_overlap_counterexample_graph.Adj p a ∧ digraph_two_overlap_counterexample_graph.Adj p b) ∨
      (∃ p, digraph_two_overlap_counterexample_graph.Adj p a ∧ digraph_two_overlap_counterexample_graph.Adj p c) ∨
      (∃ p, digraph_two_overlap_counterexample_graph.Adj p b ∧ digraph_two_overlap_counterexample_graph.Adj p c) := by
  decide
