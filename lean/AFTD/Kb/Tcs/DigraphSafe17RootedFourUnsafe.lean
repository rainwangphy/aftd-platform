import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph

/-!
# digraph_safe17_rooted_four_unsafe

Topic: graphs   Node: 92353378558a

Provenance: helper lemma. Finite safe-cycle obstruction for OP-110; experiment 13260.

Every directed four-cycle through zero in the displayed graph has an outside vertex pointing to at least three of its vertices.
-/

private instance in504_safe17_decAdj_2 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

theorem digraph_safe17_rooted_four_unsafe :
    ∀ a b c : Fin 17,
      digraph_safe17_graph.Adj 0 a → digraph_safe17_graph.Adj a b →
      digraph_safe17_graph.Adj b c → digraph_safe17_graph.Adj c 0 →
      ∃ x : Fin 17, x ≠ 0 ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c ∧
        ((digraph_safe17_graph.Adj x 0 ∧ digraph_safe17_graph.Adj x a ∧
          digraph_safe17_graph.Adj x b) ∨
         (digraph_safe17_graph.Adj x 0 ∧ digraph_safe17_graph.Adj x a ∧
          digraph_safe17_graph.Adj x c) ∨
         (digraph_safe17_graph.Adj x 0 ∧ digraph_safe17_graph.Adj x b ∧
          digraph_safe17_graph.Adj x c) ∨
         (digraph_safe17_graph.Adj x a ∧ digraph_safe17_graph.Adj x b ∧
          digraph_safe17_graph.Adj x c)) := by
  decide
