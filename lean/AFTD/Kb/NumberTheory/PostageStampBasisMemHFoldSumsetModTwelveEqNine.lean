import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampBasisRepModTwelveEqNine
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetOfList

/-!
# postage_stamp_basis_mem_h_fold_sumset_mod_twelve_eq_nine

Topic: elementary_number_theory   Node: 1ffa63373d9c

Provenance: helper lemma. step towards postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine

For any r : ℕ and any m ≤ 36r² + 72r + 33, m belongs to the (12r+9)-fold sumset of {-(2r+2), 2r+2, 4r+5}.
-/

/-- Every integer m ≤ 36r² + 72r + 33 belongs to the (12r+9)-fold sumset of {-(2r+2), 2r+2, 4r+5}. -/
theorem postage_stamp_basis_mem_h_fold_sumset_mod_twelve_eq_nine (r : ℕ) (m : ℕ)
    (hm : m ≤ 36 * r ^ 2 + 72 * r + 33) :
    int_mem_h_fold_sumset (12 * r + 9)
      {-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5} (m : ℤ) := by
  obtain ⟨s, t, u, hstu, hsum⟩ := postage_stamp_basis_rep_mod_twelve_eq_nine r m hm
  let l : List ℤ :=
    List.replicate s (-(2 * (r : ℤ) + 2)) ++ List.replicate t (2 * (r : ℤ) + 2) ++
      List.replicate u (4 * (r : ℤ) + 5)
  have hlen : l.length = 12 * r + 9 := by
    simp only [l, List.length_append, List.length_replicate]
    omega
  have hsuml : l.sum = (m : ℤ) := by
    simp only [l, List.sum_append, List.sum_replicate, nsmul_eq_mul]
    linarith [hsum]
  have hmem : ∀ x ∈ l, x ∈ ({-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5} : Finset ℤ) := by
    intro x hx
    simp only [l, List.mem_append, List.mem_replicate] at hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨_, rfl⟩ := hx; simp
    · obtain ⟨_, rfl⟩ := hx; simp
    · obtain ⟨_, rfl⟩ := hx; simp
  rw [← hlen, ← hsuml]
  exact int_mem_h_fold_sumset_of_list _ l hmem
