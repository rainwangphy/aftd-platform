import AFTD.Prelude
import AFTD.Kb.Tcs.TwoDisjointGroupFamilyFitsTwoSlots
import AFTD.Kb.Tcs.PairwiseDisjointNonemptyGroupsCardBound
import AFTD.Kb.Tcs.Op1957TwoExceptionalGroupsExactBlockPool

/-!
# two_exceptional_groups_and_block_pool

Topic: graphs   Node: 4d7be61663a4

Provenance: helper lemma. OP-1957; grouping the saturated barrier reservoir into at most two exceptional groups and a B-only pool.

For a pairwise disjoint family of nonempty finite sets with at most two members meeting the complement of B, split its indices into B-only groups and two possibly empty exceptional slots. The slots and B-only groups are disjoint, the number of occupied slots plus B-only groups is the original count, and the B-only union has at least as many vertices as groups.
-/

theorem two_exceptional_groups_and_block_pool
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (K : Finset I) (F : I → Finset V) (B : Finset V)
    (hne : ∀ i ∈ K, (F i).Nonempty)
    (hdis : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (F i) (F j))
    (houtside : (K.filter (fun i => (F i \ B).Nonempty)).card ≤ 2) :
    ∃ J ⊆ K, ∃ P Q : Finset V,
      (∀ i ∈ J, F i ⊆ B) ∧
      (P = ∅ ∨ ∃ i ∈ K \ J, P = F i) ∧
      (Q = ∅ ∨ ∃ i ∈ K \ J, Q = F i) ∧
      (∀ i ∈ K \ J, F i = P ∨ F i = Q) ∧
      Disjoint P Q ∧
      (∀ i ∈ J, Disjoint (F i) P ∧ Disjoint (F i) Q) ∧
      J.card + (if P.Nonempty then 1 else 0) +
        (if Q.Nonempty then 1 else 0) = K.card ∧
      J.card ≤ (J.biUnion F).card := by
  obtain ⟨J,hJK,P,Q,hJB,_,hP,hQ,hslots,hPQ,hJPQ,hcount,hbound⟩ :=
    op1957_two_exceptional_groups_exact_block_pool K F B hne hdis houtside
  exact ⟨J,hJK,P,Q,hJB,hP,hQ,hslots,hPQ,hJPQ,hcount,hbound⟩
