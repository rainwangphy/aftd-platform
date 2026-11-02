import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_common_predecessor_seven_bounded_indegree_degree_bound

Topic: graphs   Node: 8b8d5b4d5ec9

Provenance: helper lemma. Auxiliary-graph transfer and counting steps for the OP-110 campaign.

If all outdegrees equal seven and all indegrees are at most seven, every vertex of the common-predecessor graph has degree at most 42.
-/

private instance in478_digraph_common_predecessor_seven_bounded_indegree_degree_bound_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_common_predecessor_seven_bounded_indegree_degree_bound (α : Type) [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hinde : ∀ v, (Finset.univ.filter fun w => D.Adj w v).card ≤ 7) :
    ∀ v, (digraph_common_predecessor_graph D).degree v ≤ 42 := by
  classical
  intro v
  let ins : Finset α := Finset.univ.filter fun w => D.Adj w v
  let outs : α → Finset α := fun w => (Finset.univ.filter fun z => D.Adj w z).erase v
  have hcover : (digraph_common_predecessor_graph D).neighborFinset v ⊆ ins.biUnion outs := by
    intro u hu
    have hu' := (SimpleGraph.mem_neighborFinset _ _ _).mp hu
    obtain ⟨hne, w, hwv, hwu⟩ := hu'
    apply Finset.mem_biUnion.mpr
    refine ⟨w, ?_, ?_⟩
    · simp [ins, hwv]
    · simp [outs, hne.symm, hwu]
  have hsize : ∀ w ∈ ins, (outs w).card = 6 := by
    intro w hw
    have hwv : D.Adj w v := (Finset.mem_filter.mp hw).2
    have he := Finset.card_erase_add_one (s := Finset.univ.filter fun z => D.Adj w z) (a := v) (by simp [hwv])
    have hd := hreg w
    change (outs w).card + 1 = _ at he
    omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    _ ≤ (ins.biUnion outs).card := Finset.card_le_card hcover
    _ ≤ ∑ w ∈ ins, (outs w).card := Finset.card_biUnion_le
    _ = ∑ _w ∈ ins, (6 : ℕ) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hsize w hw
    _ = 6 * ins.card := by simp [Nat.mul_comm]
    _ ≤ 42 := by have h := hinde v; change ins.card ≤ 7 at h; omega
