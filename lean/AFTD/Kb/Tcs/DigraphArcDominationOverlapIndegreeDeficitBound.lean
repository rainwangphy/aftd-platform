import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphOrientedDegreeDeficitOverlapBudget

/-!
# digraph_arc_domination_overlap_indegree_deficit_bound

Topic: graphs   Node: f7111a97bbca

Provenance: helper lemma. Overlap-to-regularity reduction in the general campaign route to OP-110.

In an oriented loopless r-outregular arc-dominated digraph, the total shortfall of indegrees below r is at most choose(z+1,2), where z is the number of repeated common-predecessor pair incidences.
-/

private instance in478_overlap_deficit_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_arc_domination_overlap_indegree_deficit_bound
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (r : ℕ) (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = r)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v) :
    (∑ v : α, (r - (Finset.univ.filter fun w => D.Adj w v).card)) ≤
      Nat.choose (Fintype.card α * Nat.choose r 2 -
        (digraph_common_predecessor_graph D).edgeFinset.card + 1) 2 := by
  classical
  have h := digraph_oriented_degree_deficit_overlap_budget α D hloop hori hdom
  simp only [hreg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  generalize hz : Fintype.card α * Nat.choose r 2 -
        (digraph_common_predecessor_graph D).edgeFinset.card = z at h ⊢
  cases z with
  | zero => simp at *; omega
  | succ z =>
    have hz : z ≤ Nat.choose (z+1) 2 := by
      rw [Nat.choose_succ_succ']
      simp
    have hc : Nat.choose (z+1+1) 2 = (z+1) + Nat.choose (z+1) 2 := by
      rw [Nat.choose_succ_succ']
      simp only [Nat.choose_one_right]
    rw [hc]
    omega
