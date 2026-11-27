import AFTD.Prelude

/-!
# two_disjoint_group_family_fits_two_slots

Topic: graphs   Node: cb36219f557e

Provenance: helper lemma. OP-1957; bookkeeping for the two exceptional groups in the saturated barrier reduction.

A family of at most two pairwise disjoint nonempty finite sets can be placed in two slots, with unused slots empty, and the number of occupied slots equals the family size.
-/

theorem two_disjoint_group_family_fits_two_slots
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
