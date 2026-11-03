import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.FiniteFamilyOverlapMultiplicityIdentity

/-!
# digraph_common_predecessor_overlap_incidence_identity

Topic: graphs   Node: 8408bb87de08

Provenance: helper lemma. Exact incidence identity needed for the small-overlap structural route to OP-110.

For a finite digraph, the total excess multiplicity of edges of its common-predecessor graph equals the sum of unordered pairs in its out-neighborhoods minus the number of distinct common-predecessor edges.
-/

private instance in504_overlap_count_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_common_predecessor_overlap_incidence_identity
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] :
    (∑ e ∈ (digraph_common_predecessor_graph D).edgeFinset,
      ((Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card - 1)) =
    (∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      (digraph_common_predecessor_graph D).edgeFinset.card := by
  classical
  let outs : α → Finset α := fun u => Finset.univ.filter (fun w => D.Adj u w)
  let N : α → Finset (Sym2 α) := fun u => (outs u).offDiag.image Sym2.mk.uncurry
  have hN : ∀ u a b, s(a,b) ∈ N u ↔ a ≠ b ∧ D.Adj u a ∧ D.Adj u b := by
    intro u a b
    constructor
    · intro h
      obtain ⟨⟨x,y⟩, hxy, he⟩ := Finset.mem_image.mp h
      obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hxy
      have hx' : D.Adj u x := (Finset.mem_filter.mp hx).2
      have hy' : D.Adj u y := (Finset.mem_filter.mp hy).2
      rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨hne,hx',hy'⟩
      · exact ⟨hne.symm,hy',hx'⟩
    · rintro ⟨hne, ha, hb⟩
      apply Finset.mem_image.mpr
      refine ⟨(a,b), Finset.mem_offDiag.mpr ?_, rfl⟩
      exact ⟨by simp [outs,ha], by simp [outs,hb], hne⟩
  have hE : (Finset.univ : Finset α).biUnion N =
      (digraph_common_predecessor_graph D).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change s(a,b) ∈ (Finset.univ : Finset α).biUnion N ↔
        a ≠ b ∧ ∃ u, D.Adj u a ∧ D.Adj u b
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hN]
      constructor
      · rintro ⟨u,hne,ha,hb⟩
        exact ⟨hne,u,ha,hb⟩
      · rintro ⟨hne,u,ha,hb⟩
        exact ⟨u,hne,ha,hb⟩
  have hparent : ∀ e ∈ (digraph_common_predecessor_graph D).edgeFinset,
      (Finset.univ.filter fun p => e ∈ N p) =
        (Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hne : a ≠ b := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact he.1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hN]
      constructor
      · rintro ⟨_,ha,hb⟩ x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact ha
        · exact hb
      · intro h
        exact ⟨hne, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  have hmain := finite_family_overlap_multiplicity_identity α (Sym2 α) Finset.univ N
  rw [hE] at hmain
  have hsum : (∑ u : α, (N u).card) =
      ∑ u : α, Nat.choose (outs u).card 2 := by
    apply Finset.sum_congr rfl
    intro u _
    exact Sym2.card_image_offDiag (outs u)
  rw [hsum] at hmain
  have hfilters :
      (∑ e ∈ (digraph_common_predecessor_graph D).edgeFinset,
        ((Finset.univ.filter fun p => e ∈ N p).card - 1)) =
      (∑ e ∈ (digraph_common_predecessor_graph D).edgeFinset,
        ((Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card - 1)) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [hparent e he]
  rw [hfilters] at hmain
  change _ = (∑ v : α, Nat.choose (outs v).card 2) - _
  omega
