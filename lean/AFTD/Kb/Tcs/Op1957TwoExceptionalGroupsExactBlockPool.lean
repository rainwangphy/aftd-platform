import AFTD.Prelude
import AFTD.Kb.Tcs.PairwiseDisjointNonemptyGroupsCardBound

/-!
# op1957_two_exceptional_groups_exact_block_pool

Topic: graphs   Node: b743d51bf8f3

Provenance: helper lemma. OP-1957: exact exceptional group pool

A disjoint family with at most two groups meeting the complement of B splits into B-only groups and two slots, with every occupied slot meeting the complement of B and the pool having at least one vertex per group.
-/

set_option maxHeartbeats 1000000

theorem in1245_two_slots
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (J : Finset I) (F : I → Finset V) (hcard : J.card ≤ 2)
    (hnonempty : ∀ i ∈ J, (F i).Nonempty)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j)) :
    ∃ P Q : Finset V,
      (P = ∅ ∨ ∃ i ∈ J, P = F i) ∧
      (Q = ∅ ∨ ∃ i ∈ J, Q = F i) ∧
      Disjoint P Q ∧ (∀ i ∈ J, F i = P ∨ F i = Q) ∧
      (if P.Nonempty then 1 else 0) + (if Q.Nonempty then 1 else 0) = J.card := by
  classical
  have cases : J.card = 0 ∨ J.card = 1 ∨ J.card = 2 := by omega
  rcases cases with hzero | hone | htwo
  · have hJ : J = ∅ := Finset.card_eq_zero.mp hzero
    subst J
    exact ⟨∅, ∅, by simp⟩
  · obtain ⟨i, hJ⟩ := Finset.card_eq_one.mp hone
    subst J
    have hi : (F i).Nonempty := hnonempty i (by simp)
    refine ⟨F i, ∅, ?_, ?_, ?_, ?_, ?_⟩
    · exact Or.inr ⟨i, by simp, rfl⟩
    · exact Or.inl rfl
    · simp
    · intro j hj
      have : j = i := by simpa using hj
      subst j
      exact Or.inl rfl
    · simp [hi]
  · obtain ⟨i,j,hij,hJ⟩ := Finset.card_eq_two.mp htwo
    subst J
    have hi : (F i).Nonempty := hnonempty i (by simp)
    have hj : (F j).Nonempty := hnonempty j (by simp)
    refine ⟨F i, F j, ?_, ?_, ?_, ?_, ?_⟩
    · exact Or.inr ⟨i, by simp, rfl⟩
    · exact Or.inr ⟨j, by simp, rfl⟩
    · exact hdis i (by simp) j (by simp) hij
    · intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> simp
    · simp [hi,hj,hij]

theorem op1957_two_exceptional_groups_exact_block_pool
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (K : Finset I) (F : I → Finset V) (B : Finset V)
    (hne : ∀ i ∈ K, (F i).Nonempty)
    (hdis : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (F i) (F j))
    (houtside : (K.filter (fun i => (F i \ B).Nonempty)).card ≤ 2) :
    ∃ J ⊆ K, ∃ P Q : Finset V,
      (∀ i ∈ J, F i ⊆ B) ∧
      (∀ i ∈ K \ J, (F i \ B).Nonempty) ∧
      (P = ∅ ∨ ∃ i ∈ K \ J, P = F i) ∧
      (Q = ∅ ∨ ∃ i ∈ K \ J, Q = F i) ∧
      (∀ i ∈ K \ J, F i = P ∨ F i = Q) ∧
      Disjoint P Q ∧
      (∀ i ∈ J, Disjoint (F i) P ∧ Disjoint (F i) Q) ∧
      J.card + (if P.Nonempty then 1 else 0) +
        (if Q.Nonempty then 1 else 0) = K.card ∧
      J.card ≤ (J.biUnion F).card := by
  classical
  let H := K.filter (fun i => (F i \ B).Nonempty)
  let J := K \ H
  have hHK : H ⊆ K := Finset.filter_subset _ _
  have hJK : J ⊆ K := Finset.sdiff_subset
  have hKH : K \ J = H := by
    ext i
    simp only [J,Finset.mem_sdiff]
    constructor
    · rintro ⟨hi,hn⟩
      by_contra hh
      exact hn ⟨hi,hh⟩
    · intro hi
      exact ⟨hHK hi,fun hh => hh.2 hi⟩
  have hJB : ∀ i ∈ J, F i ⊆ B := by
    intro i hi v hv
    have hiK := hJK hi
    have hiH : i ∉ H := (Finset.mem_sdiff.mp hi).2
    by_contra hvB
    apply hiH
    exact Finset.mem_filter.mpr ⟨hiK,⟨v,Finset.mem_sdiff.mpr ⟨hv,hvB⟩⟩⟩
  have hnH : ∀ i ∈ H, (F i).Nonempty := fun i hi => hne i (hHK hi)
  have hdH : ∀ i ∈ H, ∀ j ∈ H, i ≠ j → Disjoint (F i) (F j) :=
    fun i hi j hj hij => hdis i (hHK hi) j (hHK hj) hij
  obtain ⟨P,Q,hP,hQ,hPQ,hslot,hcount⟩ := in1245_two_slots H F houtside hnH hdH
  have hJdis : ∀ i ∈ J, ∀ j ∈ H, Disjoint (F i) (F j) := by
    intro i hi j hj
    have hneij : i ≠ j := by
      intro he; subst j; exact (Finset.mem_sdiff.mp hi).2 hj
    exact hdis i (hJK hi) j (hHK hj) hneij
  have hPJ : ∀ i ∈ J, Disjoint (F i) P := by
    intro i hi
    rcases hP with hp | ⟨j,hj,hp⟩
    · simp [hp]
    · rw [hp]; exact hJdis i hi j hj
  have hQJ : ∀ i ∈ J, Disjoint (F i) Q := by
    intro i hi
    rcases hQ with hq | ⟨j,hj,hq⟩
    · simp [hq]
    · rw [hq]; exact hJdis i hi j hj
  have hcard : J.card + H.card = K.card := Finset.card_sdiff_add_card_eq_card hHK
  have hbound : J.card ≤ (J.biUnion F).card := by
    by_cases hJ : J.Nonempty
    · obtain ⟨j,hj⟩ := hJ
      have hh := pairwise_disjoint_nonempty_groups_card_bound J F j hj
        (fun i hi l hl hil => hdis i (hJK hi) l (hJK hl) hil)
        (fun i hi => hne i (hJK hi))
      have hpos : 1 ≤ (F j).card := Finset.card_pos.mpr (hne j (hJK hj))
      omega
    · have hJ0 : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      simp [hJ0]
  refine ⟨J,hJK,P,Q,hJB,?_,?_,?_,?_,hPQ,?_,?_,hbound⟩
  · intro i hi
    have hiH : i ∈ H := hKH ▸ hi
    exact (Finset.mem_filter.mp hiH).2
  · simpa [hKH] using hP
  · simpa [hKH] using hQ
  · simpa [hKH] using hslot
  · exact fun i hi => ⟨hPJ i hi,hQJ i hi⟩
  · omega
