import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.CyclicCubicSyndrome

/-!
# cyclic_cubic_parity_repr_nonempty

Topic: quantum   Node: e1ae415faeee

Provenance: helper lemma. step towards cyclic_cubic_t_count_isotropy_lower_bound

Every parity representation S of cyclic_cubic_syndrome n for n ≥ 6 is nonempty, because cyclic_cubic_syndrome n {0, 1, 2} = 1.
-/

/-- Every parity representation of the cyclic cubic syndrome for n ≥ 6 is nonempty because the syndrome at {0, 1, 2} equals 1. -/
theorem cyclic_cubic_parity_repr_nonempty (n : ℕ) (hn : 6 ≤ n) (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (cyclic_cubic_syndrome n)) : S.Nonempty := by
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
  have h_syn : cyclic_cubic_syndrome n A = 1 := by
    unfold cyclic_cubic_syndrome
    have h : ∃ j : Fin n,
      have hn_pos : 0 < n := by have := j.isLt; omega
      A = {j, ⟨(j.val + 1) % n, Nat.mod_lt _ hn_pos⟩, ⟨(j.val + 2) % n, Nat.mod_lt _ hn_pos⟩} := by
      refine ⟨⟨0, by omega⟩, ?_⟩
      dsimp [A]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have h1 : (⟨(0 + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = ⟨1, by omega⟩ := by
        ext; simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      have h2 : (⟨(0 + 2) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = ⟨2, by omega⟩ := by
        ext; simp [Nat.mod_eq_of_lt (by omega : 2 < n)]
      rw [h1, h2]
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
