import AFTD.Prelude
import AFTD.Kb.Tcs.PairwiseDisjointNonemptyGroupsCardBound

/-!
# op1957_odd_group_intersection_defect_bound

Topic: graphs   Node: b13a0fa4d7e7

Provenance: helper lemma. OP-1957: one-defect boundary graph-to-count transfer, arXiv:2611.22690

For disjoint odd finite groups, the number of groups is at most the number with odd intersection with B plus the number of pool vertices outside B.
-/

theorem op1957_odd_group_intersection_defect_bound
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (B : Finset V) (K : Finset I) (T : I → Finset V)
    (hTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (T i) (T j))
    (hodd : ∀ i ∈ K, Odd (T i).card) :
    K.card ≤ (K.filter (fun i => Odd ((T i) ∩ B).card)).card + (K.biUnion T \ B).card := by
  classical
  let E := K.filter (fun i => Odd ((T i) ∩ B).card)
  let H := K.filter (fun i => ¬ Odd ((T i) ∩ B).card)
  let F : I → Finset V := fun i => T i \ B
  have hHK : H ⊆ K := Finset.filter_subset _ _
  have hne : ∀ i ∈ H, (F i).Nonempty := by
    intro i hi
    have hn := (Finset.mem_filter.mp hi).2
    by_contra h
    have hzero : F i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hsub : T i ⊆ B := Finset.sdiff_eq_empty_iff_subset.mp hzero
    have heq : T i ∩ B = T i := Finset.inter_eq_left.mpr hsub
    apply hn
    rw [heq]
    exact hodd i (hHK hi)
  have hdis : ∀ i ∈ H, ∀ j ∈ H, i ≠ j → Disjoint (F i) (F j) := by
    intro i hi j hj hij
    exact Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset (hTT i (hHK hi) j (hHK hj) hij))
  have hsub : H.biUnion F ⊆ K.biUnion T \ B := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := Finset.mem_biUnion.mp hz
    have hzi' := Finset.mem_sdiff.mp hzi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i,hHK hi,hzi'.1⟩,hzi'.2⟩
  have hHcard : H.card ≤ (K.biUnion T \ B).card := by
    by_cases hh : H.Nonempty
    · obtain ⟨j,hj⟩ := hh
      have hr := pairwise_disjoint_nonempty_groups_card_bound H F j hj hdis hne
      have hp := Finset.card_pos.mpr (hne j hj)
      have hs := Finset.card_le_card hsub
      omega
    · have he : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
      simp [he]
  have heq : E.card+H.card=K.card := by
    exact Finset.card_filter_add_card_filter_not (s:=K) (fun i => Odd ((T i) ∩ B).card)
  change K.card ≤ E.card + (K.biUnion T \ B).card
  omega
