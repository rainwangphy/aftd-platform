import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.LineSyndrome

/-!
# line_cubic_parity_repr_nonempty

Topic: quantum   Node: 46da4959d69a

Provenance: helper lemma. step towards line_cubic_t_count_lower_bound

Every parity representation of the line cubic syndrome for n ≥ 5 is nonempty, because line_syndrome n {0, 1, 2} = 1.
-/

/-- Every parity representation of the line cubic syndrome for n ≥ 5 is nonempty. -/
theorem line_cubic_parity_repr_nonempty (n : ℕ) (hn : 5 ≤ n)
    (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (line_syndrome n)) :
    S.Nonempty := by
  let A : Finset (Fin n) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hA_card : A.card = 3 := by
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
      intro h; injection h with h; omega
    have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
      intro h; injection h with h; omega
    have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
      intro h; injection h with h; omega
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · intro h; simp only [Finset.mem_singleton] at h; exact h12 h
    · simp only [Finset.mem_insert, Finset.mem_singleton]; rintro (h | h)
      · exact h01 h
      · exact h02 h
  have h_syn : line_syndrome n A = 1 := by
    unfold line_syndrome
    have h : ∃ i : Fin (n - 2), A = {⟨i.1, by omega⟩, ⟨i.1 + 1, by omega⟩, ⟨i.1 + 2, by omega⟩} := by
      refine ⟨⟨0, by omega⟩, ?_⟩
      rfl
    exact if_pos h
  have h_repr := hS.2 A ⟨by omega, by omega⟩
  rw [h_syn] at h_repr
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  have h_sub_empty : {y ∈ S | A ⊆ y} = ∅ := by
    rw [h_empty]
    exact Finset.filter_empty _
  rw [h_sub_empty, Finset.card_empty] at h_repr
  revert h_repr
  decide
