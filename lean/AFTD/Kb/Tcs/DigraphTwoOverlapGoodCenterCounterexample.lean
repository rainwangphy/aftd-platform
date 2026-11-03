import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphTwoOverlapCounterexampleGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_two_overlap_good_center_counterexample

Topic: graphs   Node: 6a1d85643013

Provenance: helper lemma. Finite counterexample discovered in experiment 13185 and independently checked in 13186; serves the OP-110 small-overlap route.

The displayed thirteen-vertex graph is loopless, oriented and arc-dominated, has common-predecessor overlap six, and has no vertex whose out-neighborhood is clean and whose every outgoing arc has a common successor. Thus the general good-center conclusion can fail even when twice the overlap is smaller than the number of vertices.
-/

private instance in504_no_good_decAdj : DecidableRel digraph_two_overlap_counterexample_graph.Adj := by
  intro u v
  unfold digraph_two_overlap_counterexample_graph
  infer_instance

private instance in504_no_good_aux_decAdj : DecidableRel (digraph_common_predecessor_graph digraph_two_overlap_counterexample_graph).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem digraph_two_overlap_good_center_counterexample :
    (∀ u, ¬ digraph_two_overlap_counterexample_graph.Adj u u) ∧
    (∀ u v, digraph_two_overlap_counterexample_graph.Adj u v → ¬ digraph_two_overlap_counterexample_graph.Adj v u) ∧
    (∀ u v, digraph_two_overlap_counterexample_graph.Adj u v →
      ∃ p, digraph_two_overlap_counterexample_graph.Adj p u ∧ digraph_two_overlap_counterexample_graph.Adj p v) ∧
    ((∑ u : Fin 13, Nat.choose (Finset.univ.filter fun v => digraph_two_overlap_counterexample_graph.Adj u v).card 2) -
      (digraph_common_predecessor_graph digraph_two_overlap_counterexample_graph).edgeFinset.card = 6) ∧
    ¬ ∃ u : Fin 13,
      (∀ a b, a ≠ b → digraph_two_overlap_counterexample_graph.Adj u a → digraph_two_overlap_counterexample_graph.Adj u b →
        ∀ p, digraph_two_overlap_counterexample_graph.Adj p a → digraph_two_overlap_counterexample_graph.Adj p b → p = u) ∧
      (∀ v, digraph_two_overlap_counterexample_graph.Adj u v →
        ∃ w, digraph_two_overlap_counterexample_graph.Adj u w ∧ digraph_two_overlap_counterexample_graph.Adj v w) := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  ·
    rintro ⟨u, hclean, hgood⟩
    fin_cases u
    · have heq := hclean 1 12 (by decide) (by decide) (by decide) 4 (by decide) (by decide)
      exact (by decide : (4 : Fin 13) ≠ 0) heq
    · have heq := hclean 2 7 (by decide) (by decide) (by decide) 0 (by decide) (by decide)
      exact (by decide : (0 : Fin 13) ≠ 1) heq
    · have heq := hclean 3 11 (by decide) (by decide) (by decide) 6 (by decide) (by decide)
      exact (by decide : (6 : Fin 13) ≠ 2) heq
    · have heq := hclean 4 8 (by decide) (by decide) (by decide) 0 (by decide) (by decide)
      exact (by decide : (0 : Fin 13) ≠ 3) heq
    · have heq := hclean 1 12 (by decide) (by decide) (by decide) 0 (by decide) (by decide)
      exact (by decide : (0 : Fin 13) ≠ 4) heq
    · have heq := hclean 2 7 (by decide) (by decide) (by decide) 0 (by decide) (by decide)
      exact (by decide : (0 : Fin 13) ≠ 5) heq
    · have heq := hclean 1 12 (by decide) (by decide) (by decide) 0 (by decide) (by decide)
      exact (by decide : (0 : Fin 13) ≠ 6) heq
    · have h := hgood 9 (by decide)
      have hn : ¬ ∃ w : Fin 13, digraph_two_overlap_counterexample_graph.Adj 7 w ∧ digraph_two_overlap_counterexample_graph.Adj 9 w := by decide
      exact hn h
    · have h := hgood 10 (by decide)
      have hn : ¬ ∃ w : Fin 13, digraph_two_overlap_counterexample_graph.Adj 8 w ∧ digraph_two_overlap_counterexample_graph.Adj 10 w := by decide
      exact hn h
    · have h := hgood 10 (by decide)
      have hn : ¬ ∃ w : Fin 13, digraph_two_overlap_counterexample_graph.Adj 9 w ∧ digraph_two_overlap_counterexample_graph.Adj 10 w := by decide
      exact hn h
    · have h := hgood 1 (by decide)
      have hn : ¬ ∃ w : Fin 13, digraph_two_overlap_counterexample_graph.Adj 10 w ∧ digraph_two_overlap_counterexample_graph.Adj 1 w := by decide
      exact hn h
    · have h := hgood 0 (by decide)
      have hn : ¬ ∃ w : Fin 13, digraph_two_overlap_counterexample_graph.Adj 11 w ∧ digraph_two_overlap_counterexample_graph.Adj 0 w := by decide
      exact hn h
    · have h := hgood 11 (by decide)
      have hn : ¬ ∃ w : Fin 13, digraph_two_overlap_counterexample_graph.Adj 12 w ∧ digraph_two_overlap_counterexample_graph.Adj 11 w := by decide
      exact hn h
