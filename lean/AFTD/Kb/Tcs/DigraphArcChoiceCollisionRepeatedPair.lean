import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphTwoCommonParentsEdgeMultiplicity

/-!
# digraph_arc_choice_collision_repeated_pair

Topic: graphs   Node: c443a3e7e15d

Provenance: helper lemma. Graph-specific collision-to-repeated-pair step for the OP-110 small-overlap route.

When two outgoing arcs of a loopless digraph receive the same chosen common predecessor, their distinct heads form an auxiliary edge with at least two common predecessors.
-/

private instance in504_collision_pair_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_arc_choice_collision_repeated_pair
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (choose : α → α → α)
    (hloop : ∀ u, ¬ D.Adj u u)
    (hchoice : ∀ u v, D.Adj u v → D.Adj (choose u v) u ∧ D.Adj (choose u v) v)
    (u a b : α) (hab : a ≠ b) (hua : D.Adj u a) (hub : D.Adj u b)
    (heq : choose u a = choose u b) :
    s(a,b) ∈ (digraph_common_predecessor_graph D).edgeFinset ∧
      2 ≤ (Finset.univ.filter fun p => ∀ x, x ∈ s(a,b) → D.Adj p x).card := by
  have hp := hchoice u a hua
  have hp' := hchoice u b hub
  have hpb : D.Adj (choose u a) b := by rw [heq]; exact hp'.2
  have hne : u ≠ choose u a := by
    intro h
    exact hloop u (by simpa [← h] using hp.1)
  exact digraph_two_common_parents_edge_multiplicity α D a b u (choose u a)
    hab hne hua hub hp.2 hpb
