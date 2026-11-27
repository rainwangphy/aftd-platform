import AFTD.Prelude

/-!
# odd_groups_single_non_block_component_count

Topic: graphs   Node: 9cc4ba1b43f7

Provenance: helper lemma. OP-1957: uniform odd-component barrier count compression.

For pairwise-disjoint odd finite groups indexed by a finite set, if all groups except one lie inside B, the number whose intersection with B has odd size is the number of groups minus one, plus one precisely when the union outside B has even size.
-/

set_option maxHeartbeats 1000000

theorem odd_groups_single_non_block_component_count
    {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (I : Finset ι) (T : ι → Finset V) (B : Finset V) (j : ι)
    (hj : j ∈ I)
    (hdis : ∀ i ∈ I, ∀ l ∈ I, i ≠ l → Disjoint (T i) (T l))
    (hodd : ∀ i ∈ I, Odd (T i).card)
    (hother : ∀ i ∈ I, i ≠ j → T i ⊆ B) :
    let R := I.biUnion T;
    (I.filter (fun i => Odd ((T i) ∩ B).card)).card + 1 =
      I.card + (if Even (R \ B).card then 1 else 0) := by
  classical
  dsimp only
  have hRdiff : I.biUnion T \ B = T j \ B := by
    ext v
    simp only [Finset.mem_sdiff,Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨i,hi,hvi⟩,hvB⟩
      by_cases hij : i=j
      · subst i; exact ⟨hvi,hvB⟩
      · exact False.elim (hvB (hother i hi hij hvi))
    · rintro ⟨hv,hvB⟩
      exact ⟨⟨j,hj,hv⟩,hvB⟩
  have hparity : Odd ((T j) ∩ B).card ↔ Even ((T j) \ B).card := by
    have hcard := Finset.card_inter_add_card_sdiff (T j) B
    have ho := hodd j hj
    constructor
    · intro ha
      rcases Nat.even_or_odd ((T j) \ B).card with hb | hb
      · exact hb
      · obtain ⟨a,ha⟩ := ha
        obtain ⟨b,hb⟩ := hb
        obtain ⟨d,hd⟩ := ho
        omega
    · intro hb
      rcases Nat.even_or_odd ((T j) ∩ B).card with ha | ha
      · obtain ⟨a,ha⟩ := ha
        obtain ⟨b,hb⟩ := hb
        obtain ⟨d,hd⟩ := ho
        omega
      · exact ha
  have hotherodd : ∀ i ∈ I, i ≠ j → Odd ((T i) ∩ B).card := by
    intro i hi hij
    rw [Finset.inter_eq_left.mpr (hother i hi hij)]
    exact hodd i hi
  by_cases hjodd : Odd ((T j) ∩ B).card
  · have hf : I.filter (fun i => Odd ((T i) ∩ B).card) = I := by
      apply Finset.filter_eq_self.mpr
      intro i hi
      by_cases hij : i=j
      · simpa [hij] using hjodd
      · exact hotherodd i hi hij
    rw [hf,hRdiff]
    simp [hparity.mp hjodd]
  · have hf : I.filter (fun i => Odd ((T i) ∩ B).card) = I.erase j := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_erase]
      constructor
      · rintro ⟨hi,ho⟩
        refine ⟨?_,hi⟩
        intro hij; subst i; exact hjodd ho
      · rintro ⟨hij,hi⟩
        exact ⟨hi,hotherodd i hi hij⟩
    have hneven : ¬ Even ((T j) \ B).card := fun h => hjodd (hparity.mpr h)
    rw [hf,hRdiff]
    simp [hneven,Finset.card_erase_add_one hj]
