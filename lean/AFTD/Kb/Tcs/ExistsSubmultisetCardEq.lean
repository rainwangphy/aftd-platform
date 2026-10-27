import AFTD.Prelude

/-!
# exists_submultiset_card_eq

Topic: combinatorics   Node: 129acf98c4b2

Provenance: helper lemma. step towards additive_basis_bound_cp_cnp_conjecture

Any multiset contains a submultiset of any cardinality less than or equal to its own.
-/

/-- Any multiset contains a submultiset of any cardinality less than or equal to its own. -/
theorem exists_submultiset_card_eq {α : Type*} (S : Multiset α) (m : ℕ) (hm : m ≤ S.card) : ∃ T : Multiset α, T ≤ S ∧ T.card = m := by
  induction S using Multiset.induction_on generalizing m with
  | empty =>
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    exact ⟨0, by simp, by simp⟩
  | cons x s ih =>
    rcases m with _ | m
    · exact ⟨0, by simp, rfl⟩
    · have hm' : m ≤ s.card := by simp only [Multiset.card_cons] at hm; omega
      obtain ⟨T, hT, hTc⟩ := ih m hm'
      exact ⟨x ::ₘ T, Multiset.cons_le_cons x hT, by simp [hTc]⟩
