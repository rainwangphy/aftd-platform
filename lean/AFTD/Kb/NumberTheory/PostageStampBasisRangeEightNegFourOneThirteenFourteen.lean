import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetOfList
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetLeOfForallLe

/-!
# postage_stamp_basis_range_eight_neg_four_one_thirteen_fourteen

Topic: elementary_number_theory   Node: 4100eb31434f

Provenance: helper lemma. Step toward postage_stamp_number_three_lt_neg (four-stamp analogue of arXiv:2610.19470, Theorems 3.3-3.4); the set was found by exhaustive search (experiments 724-726).

The set A = {−4, 1, 13, 14} is an 8-basis for 99: every integer in [0, 99] is a sum of exactly 8 elements of A, so n_8(A) ≥ 99.
-/

theorem postage_stamp_basis_range_eight_neg_four_one_thirteen_fourteen :
    99 ≤ postage_stamp_basis_range 8 {-4, 1, 13, 14} := by
  have key : ∀ m : ℕ, m ≤ 99 → ∃ i j k : Fin 9, i.val + j.val + k.val ≤ 8 ∧
      (m : ℤ) = -4 * (8 - i.val - j.val - k.val : ℕ) + i.val + 13 * j.val + 14 * k.val := by
    decide +kernel
  apply le_csSup
  · refine ⟨112, fun n hn => ?_⟩
    have := int_mem_h_fold_sumset_le_of_forall_le 8 _ 14 (by decide) _ (hn n le_rfl)
    omega
  · intro m hm
    obtain ⟨i, j, k, hijk, he⟩ := key m hm
    have := int_mem_h_fold_sumset_of_list {-4, 1, 13, 14}
      (List.replicate (8 - i.val - j.val - k.val) (-4) ++ List.replicate i.val 1 ++
        List.replicate j.val 13 ++ List.replicate k.val 14) (by
          intro x hx
          simp only [List.mem_append, List.mem_replicate] at hx
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega)
    have hlen : (List.replicate (8 - i.val - j.val - k.val) (-4) ++ List.replicate i.val 1 ++
        List.replicate j.val 13 ++ List.replicate k.val (14 : ℤ)).length = 8 := by
      simp only [List.length_append, List.length_replicate]; omega
    rw [hlen] at this
    convert this using 1
    simp only [List.sum_append, List.sum_replicate, smul_eq_mul]
    rw [he]; push_cast; ring
