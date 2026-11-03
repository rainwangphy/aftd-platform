import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph

/-!
# digraph_safe17_shift

Topic: graphs   Node: 3067065988cc

Provenance: helper lemma. Finite safe-cycle obstruction for OP-110; experiment 13260.

The displayed cyclic graph is invariant under translating both endpoints.
-/

private instance in504_safe17_decAdj_4 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

theorem digraph_safe17_shift (a b t : Fin 17) :
    digraph_safe17_graph.Adj (a+t) (b+t) ↔ digraph_safe17_graph.Adj a b := by
  change ((b+t)-(a+t)).val ∈ ({1,2,3,5,6,7,13} : Finset ℕ) ↔
    (b-a).val ∈ ({1,2,3,5,6,7,13} : Finset ℕ)
  rw [add_sub_add_right_eq_sub]
