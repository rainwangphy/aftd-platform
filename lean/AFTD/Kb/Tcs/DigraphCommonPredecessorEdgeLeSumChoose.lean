import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_common_predecessor_edge_le_sum_choose

Topic: graphs   Node: 7a19fe7a8bde

Provenance: helper lemma. General form of the auxiliary edge count in arXiv:2610.11517, Proposition 4.3.

The common-predecessor graph has at most the sum over vertices of the number of pairs in each out-neighborhood.
-/

private instance in478_general_edge_count_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_common_predecessor_edge_le_sum_choose
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] :
    (digraph_common_predecessor_graph D).edgeFinset.card ≤
      ∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2 := by
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
  calc
    (digraph_common_predecessor_graph D).edgeFinset.card ≤
        ((Finset.univ : Finset α).biUnion edgesAt).card := Finset.card_le_card hcover
    _ ≤ ∑ v ∈ (Finset.univ : Finset α), (edgesAt v).card := Finset.card_biUnion_le
    _ = ∑ v : α, Nat.choose (outs v).card 2 := by
      apply Finset.sum_congr rfl
      intro v _
      exact Sym2.card_image_offDiag (outs v)
