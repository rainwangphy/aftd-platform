import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.IntMemHFoldSumset

/-!
# postage_stamp_number_neg_two_of_odd_range_lt

Topic: elementary_number_theory   Node: 97c4bef10c69

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

If a set does not h-fold cover [0, R] (R > 0), its h-range is less than R.
-/

theorem postage_stamp_number_neg_two_of_odd_range_lt (h R : ℕ) (A : Finset ℤ) (hR : 0 < R)
    (key : ¬ ∀ n : ℕ, n ≤ R → int_mem_h_fold_sumset h A n) :
    postage_stamp_basis_range h A + 1 ≤ R := by
  have : postage_stamp_basis_range h A ≤ R - 1 := by
    rw [postage_stamp_basis_range]
    by_cases hne : {n : ℕ | ∀ k : ℕ, k ≤ n → int_mem_h_fold_sumset h A k}.Nonempty
    · apply csSup_le hne
      intro n hn
      by_contra hcon
      push Not at hcon
      apply key
      intro k hk
      exact hn k (by omega)
    · have hempty : {n : ℕ | ∀ k : ℕ, k ≤ n → int_mem_h_fold_sumset h A k} = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      simp
  omega
