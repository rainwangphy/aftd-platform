import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_common_predecessor_graph_edge_count_le

Topic: graphs   Node: 37c0f5963efa

Provenance: helper lemma. Counting auxiliary-graph edges by out-neighborhoods, as in arXiv:2610.11517, Proposition 4.3.

If every vertex of a finite digraph has at most seven out-neighbors, then its common-predecessor graph has at most 21 times as many edges as there are vertices.
-/

private instance {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_common_predecessor_graph_edge_count_le
    (α : Type) [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hdeg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card ≤ 7) :
    (digraph_common_predecessor_graph D).edgeFinset.card ≤ 21 * Fintype.card α := by
  classical
  let outs : α → Finset α := fun v => Finset.univ.filter (fun w => D.Adj v w)
  let edgesAt : α → Finset (Sym2 α) := fun v => (outs v).offDiag.image Sym2.mk.uncurry
  have hcover : (digraph_common_predecessor_graph D).edgeFinset ⊆
      (Finset.univ : Finset α).biUnion edgesAt := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      obtain ⟨hne, w, hwu, hwv⟩ := he
      apply Finset.mem_biUnion.mpr
      refine ⟨w, Finset.mem_univ _, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨(u,v), ?_, rfl⟩
      apply Finset.mem_offDiag.mpr
      refine ⟨?_, ?_, hne⟩
      · simp [outs, hwu]
      · simp [outs, hwv]
  have hsmall : ∀ v, (edgesAt v).card ≤ 21 := by
    intro v
    change ((outs v).offDiag.image Sym2.mk.uncurry).card ≤ 21
    rw [Sym2.card_image_offDiag]
    have h := Nat.choose_le_choose 2 (hdeg v)
    exact h
  calc
    (digraph_common_predecessor_graph D).edgeFinset.card ≤
        ((Finset.univ : Finset α).biUnion edgesAt).card := Finset.card_le_card hcover
    _ ≤ ∑ v ∈ (Finset.univ : Finset α), (edgesAt v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ (Finset.univ : Finset α), 21 := Finset.sum_le_sum (by intros; exact hsmall _)
    _ = 21 * Fintype.card α := by simp [Nat.mul_comm]
