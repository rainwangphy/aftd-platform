import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange

/-!
# postage_stamp_basis_range_one_zero_one_two

Topic: elementary_number_theory   Node: 50a3aa3bac40

Provenance: helper lemma. Sanity lemma for n_h(A), arXiv:2610.19470 (Positivity and negativity for h-bases for n).

Sanity check: with h = 1, A = {0, 1, 2} covers exactly [0, 2], so n_1(A) = 2.
-/

lemma postage_stamp_basis_range_one_zero_one_two_mem_one (A : Finset ℤ) (m : ℤ) :
    int_mem_h_fold_sumset 1 A m ↔ m ∈ A := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    have : (∑ i : Fin 1, f i) = f 0 := Fin.sum_univ_one f
    rw [this]
    exact hf 0
  · intro hm
    refine ⟨fun _ => m, fun _ => hm, ?_⟩
    simp

theorem postage_stamp_basis_range_one_zero_one_two :
    postage_stamp_basis_range 1 {0, 1, 2} = 2 := by
  have h_greatest : IsGreatest {n : ℕ | ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset 1 {0, 1, 2} m} 2 := by
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [postage_stamp_basis_range_one_zero_one_two_mem_one]
      interval_cases m <;> decide
    · intro n hn
      by_contra! h
      have h3 : 3 ≤ n := by omega
      have h_in := hn 3 h3
      rw [postage_stamp_basis_range_one_zero_one_two_mem_one] at h_in
      revert h_in
      decide
  exact h_greatest.csSup_eq
