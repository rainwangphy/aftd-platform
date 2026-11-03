import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph

/-!
# digraph_safe17_structure

Topic: graphs   Node: d2c1941f8ba7

Provenance: helper lemma. Finite safe-cycle obstruction for OP-110; experiment 13260.

The displayed graph is oriented and seven-diregular, and every two distinct vertices have a common predecessor.
-/

private instance in504_safe17_decAdj_0 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

theorem digraph_safe17_structure :
    (∀ u, ¬ digraph_safe17_graph.Adj u u) ∧
    (∀ u v, digraph_safe17_graph.Adj u v → ¬ digraph_safe17_graph.Adj v u) ∧
    (∀ u, (Finset.univ.filter fun v => digraph_safe17_graph.Adj u v).card = 7) ∧
    (∀ v, (Finset.univ.filter fun u => digraph_safe17_graph.Adj u v).card = 7) ∧
    (∀ u v, u ≠ v → ∃ p, digraph_safe17_graph.Adj p u ∧ digraph_safe17_graph.Adj p v) := by
  decide
