import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_common_predecessor_degree_le_indegree_mul

Topic: graphs   Node: 2f479c9c0b75

Provenance: helper lemma. Auxiliary-graph transfer and counting steps for the OP-110 campaign.

In an r-outregular finite digraph, the degree of a vertex in the common-predecessor graph is at most (r−1) times its directed indegree.
-/

private instance in478_digraph_common_predecessor_degree_le_indegree_mul_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_common_predecessor_degree_le_indegree_mul (α : Type) [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (r : ℕ) (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = r) :
    ∀ v, (digraph_common_predecessor_graph D).degree v ≤
      (r - 1) * (Finset.univ.filter fun w => D.Adj w v).card := by
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
  have hsize : ∀ w ∈ ins, (outs w).card = r - 1 := by
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
    _ = ∑ _w ∈ ins, (r - 1) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hsize w hw
    _ = (r - 1) * ins.card := by simp [Nat.mul_comm]
    _ = (r - 1) * (Finset.univ.filter fun w => D.Adj w v).card := rfl
