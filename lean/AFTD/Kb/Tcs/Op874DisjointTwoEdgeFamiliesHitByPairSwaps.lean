import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FourTwoIncidenceTwoPseudoforestCover
import AFTD.Kb.Tcs.FiniteTwoAppearancesSystemOfDistinctRepresentatives

/-!
# op874_disjoint_two_edge_families_hit_by_pair_swaps

Topic: graphs   Node: 78b257bd4886

Provenance: helper lemma. Ownership reduction for OP-874, motivated by https://arxiv.org/abs/2610.41950 and experiment 41563.

If the edges are partitioned into paired assignments f and g, g avoids required edges, and disjoint edge families each contain at least two nonrequired edges, then independently swapping some pairs preserves all required edges on the f side and makes the g side meet every family.
-/

theorem op874_disjoint_two_edge_families_hit_by_pair_swaps
    {L E I : Type*} [Fintype L] [Fintype E] [Fintype I]
    [DecidableEq L] [DecidableEq E] [DecidableEq I]
    (f g : L → E) (S : Finset E) (C : I → Finset E)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hdisjoint : ∀ x y, f x ≠ g y)
    (hcover : ∀ e, ∃ l, f l = e ∨ g l = e)
    (hgS : ∀ l, g l ∉ S)
    (hCdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hCtwo : ∀ i, 2 ≤ ((C i).filter fun e => e ∉ S).card) :
    ∃ swap : L → Bool,
      (∀ l, f l ∈ S → swap l = false) ∧
      ∀ i, ∃ l, (if swap l then f l else g l) ∈ C i := by
  classical
  let U : I → Finset E := fun i => (C i).filter fun e => e ∉ S
  let A : I → Finset L := fun i => Finset.univ.filter fun l => f l ∈ U i ∨ g l ∈ U i
  have hall : ∀ J : Finset I, J.card ≤ (J.biUnion A).card := by
    intro J
    let N := J.biUnion A
    let T := J.biUnion U
    have hdis : (↑J : Set I).PairwiseDisjoint U := by
      intro i hi j hj hij
      exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hCdisjoint i j hij))
    have hsum : 2 * J.card ≤ ∑ i ∈ J, (U i).card := by
      calc
        _ = ∑ _i ∈ J, 2 := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum (by intro i hi; exact hCtwo i)
    have hTcard : T.card = ∑ i ∈ J, (U i).card := Finset.card_biUnion hdis
    have hsub : T ⊆ N.image f ∪ N.image g := by
      intro e he
      obtain ⟨i,hi,hei⟩ := Finset.mem_biUnion.mp he
      obtain ⟨l,hl | hl⟩ := hcover e
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨l,?_,hl⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨i,hi,by simp [A,hl,hei]⟩
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨l,?_,hl⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨i,hi,by simp [A,hl,hei]⟩
    have hupper : T.card ≤ 2*N.card := by
      calc
        _ ≤ (N.image f ∪ N.image g).card := Finset.card_le_card hsub
        _ ≤ (N.image f).card + (N.image g).card := Finset.card_union_le _ _
        _ ≤ N.card + N.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ = 2*N.card := by omega
    change J.card ≤ N.card
    omega
  obtain ⟨r,hrinj,hrmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' A).mp hall
  let swap : L → Bool := fun l => decide (∃ i : I, r i = l ∧ f l ∈ U i)
  refine ⟨swap,?_,?_⟩
  · intro l hl
    have hn : ¬ ∃ i : I, r i = l ∧ f l ∈ U i := by
      rintro ⟨i,hi,hui⟩
      exact (Finset.mem_filter.mp hui).2 hl
    simp [swap,hn]
  · intro i
    refine ⟨r i,?_⟩
    have hi : f (r i) ∈ U i ∨ g (r i) ∈ U i := by
      simpa [A] using hrmem i
    by_cases hfi : f (r i) ∈ U i
    · have hex : ∃ j : I, r j = r i ∧ f (r i) ∈ U j := ⟨i,rfl,hfi⟩
      have hsw : swap (r i) = true := by simp [swap,hex]
      simpa [hsw] using (Finset.mem_filter.mp hfi).1
    · have hgi : g (r i) ∈ U i := hi.resolve_left hfi
      have hn : ¬ ∃ j : I, r j = r i ∧ f (r i) ∈ U j := by
        rintro ⟨j,hj,hf⟩
        have hji : j=i := hrinj hj
        subst j
        exact hfi hf
      have hsw : swap (r i) = false := by simp [swap,hn]
      simpa [hsw] using (Finset.mem_filter.mp hgi).1
