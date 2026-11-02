import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraphConnected
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraphIndepFreeFour
import AFTD.Kb.Tcs.DigraphCommonPredecessorBalancedSevenCardLe121

/-!
# digraph_balanced_seven_large_forces_four_cycles_conditional

Topic: graphs   Node: b0479d674ce6

Provenance: helper lemma. Auxiliary-graph transfer and counting steps for the OP-110 campaign.

A strongly connected loopless 7-outregular digraph on at least 122 vertices whose indegrees are at most seven has four disjoint directed cycles, provided every arc is dominated and every in-neighborhood contains a directed cycle.
-/

private instance in478_digraph_balanced_seven_large_forces_four_cycles_conditional_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_balanced_seven_large_forces_four_cycles_conditional (α : Type) [Fintype α] [DecidableEq α] [Nonempty α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hinde : ∀ v, (Finset.univ.filter fun w => D.Adj w v).card ≤ 7)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (hstrong : ∀ u v, Relation.ReflTransGen D.Adj u v)
    (hin : ∀ a, ∃ C : Finset α, digraph_directed_cycle_on D C ∧ ∀ v ∈ C, D.Adj v a)
    (hsize : 122 ≤ Fintype.card α) :
    ∃ s : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  classical
  by_contra hno
  have hc := digraph_common_predecessor_graph_connected α D hloop hdom hstrong
  have hi := digraph_common_predecessor_graph_indep_free_four α D hin hno
  have hb := digraph_common_predecessor_balanced_seven_card_le_121 α D hreg hinde hc hi
  omega
