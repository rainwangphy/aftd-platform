import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorEdgeLeSumChoose
import AFTD.Kb.Tcs.OrientedOverlapMultiplicityBudget
import AFTD.Kb.Tcs.DigraphGoodCenterFromArcMapBudget
import AFTD.Kb.Tcs.DigraphOrientedArcMapMissingDirtyBudget

/-!
# digraph_oriented_small_overlap_good_center

Topic: graphs   Node: ee96e1479c8a

Provenance: helper lemma. General small-overlap center argument for OP-110; nontrivial oriented cyclic checks in experiment 12695.

In an oriented arc-dominated digraph, if repeated common-predecessor pair incidences are less than one third of the order, some vertex has a clean out-neighborhood and every outgoing arc has a common successor.
-/

private instance in478_decadj_digraph_oriented_small_overlap_good_center {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_oriented_small_overlap_good_center
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (hsmall : 3 * ((∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      (digraph_common_predecessor_graph D).edgeFinset.card) < Fintype.card α) :
    ∃ v, (∀ a b, a ≠ b → D.Adj v a → D.Adj v b →
        ∀ x, D.Adj x a → D.Adj x b → x = v) ∧
      (∀ w, D.Adj v w → ∃ x, D.Adj v x ∧ D.Adj w x) := by
  classical
  have hn : 0 < Fintype.card α := by omega
  letI : Nonempty α := Fintype.card_pos_iff.mp hn
  let choose : α → α → α := fun u v =>
    if h : D.Adj u v then Classical.choose (hdom u v h) else Classical.choice ‹Nonempty α›
  have hc : ∀ u v, D.Adj u v → D.Adj (choose u v) u ∧ D.Adj (choose u v) v := by
    intro u v huv
    simpa [choose, huv] using Classical.choose_spec (hdom u v huv)
  have hbudget := digraph_oriented_arc_map_missing_dirty_budget α D choose hloop hori hc
  have hstrict := lt_of_le_of_lt hbudget hsmall
  exact digraph_good_center_from_arc_map_budget α D choose hc hstrict
