import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphTwoOverlapCounterexampleGraph
import AFTD.Kb.Tcs.DigraphTwoOverlapGoodCenterCounterexample
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_two_overlap_good_center_criterion_false

Topic: graphs   Node: 988d40a99d0c

Provenance: helper lemma. Refutation of a stronger 2z good-center route for OP-110, using the explicit counterexample from experiments 13185 and 13186.

It is false that every oriented arc-dominated loopless digraph on thirteen vertices with twice its common-predecessor overlap below thirteen has a vertex with a clean out-neighborhood whose outgoing arcs all have common successors.
-/

private instance in504_all_graph_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

private instance in504_counterexample_decAdj : DecidableRel digraph_two_overlap_counterexample_graph.Adj := by
  intro u v
  unfold digraph_two_overlap_counterexample_graph
  infer_instance

theorem digraph_two_overlap_good_center_criterion_false :
    ¬ ∀ (D : Digraph (Fin 13)) [DecidableRel D.Adj],
      (∀ u, ¬ D.Adj u u) →
      (∀ u v, D.Adj u v → ¬ D.Adj v u) →
      (∀ u v, D.Adj u v → ∃ p, D.Adj p u ∧ D.Adj p v) →
      2 * ((∑ u : Fin 13, Nat.choose (Finset.univ.filter fun v => D.Adj u v).card 2) -
        (digraph_common_predecessor_graph D).edgeFinset.card) < Fintype.card (Fin 13) →
      ∃ u : Fin 13,
        (∀ a b, a ≠ b → D.Adj u a → D.Adj u b →
          ∀ p, D.Adj p a → D.Adj p b → p = u) ∧
        (∀ v, D.Adj u v → ∃ w, D.Adj u w ∧ D.Adj v w) := by
  intro h
  obtain ⟨hloop, hori, hdom, hz, hnot⟩ := digraph_two_overlap_good_center_counterexample
  apply hnot
  apply h digraph_two_overlap_counterexample_graph hloop hori hdom
  decide
