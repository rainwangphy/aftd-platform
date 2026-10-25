import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddSumRepr
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_is_coprime_of_mem

Topic: elementary_number_theory   Node: f5a2ecc1e7e0

Provenance: helper lemma. step towards postage_stamp_basis_range_add_two_le_of_neg_of_odd

If 0 and 1 are both in the h-fold sumset of {a, a+x, a+y} with distinct elements, then x and y are coprime.
-/

/-- Coprimality of step differences x and y from the sumset covering 0 and 1. -/
theorem postage_stamp_is_coprime_of_mem (h : ℕ) (a x y : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (h0 : int_mem_h_fold_sumset h {a, a + x, a + y} 0)
    (h1 : int_mem_h_fold_sumset h {a, a + x, a + y} 1) :
    IsCoprime x y := by
  obtain ⟨f0, hf0, eq0⟩ := h0
  obtain ⟨f1, hf1, eq1⟩ := h1
  obtain ⟨s0, t0, -, repr0⟩ := postage_stamp_number_neg_two_of_odd_sum_repr h a x y hx hy hxy f0 hf0
  obtain ⟨s1, t1, -, repr1⟩ := postage_stamp_number_neg_two_of_odd_sum_repr h a x y hx hy hxy f1 hf1
  rw [eq0] at repr0
  rw [eq1] at repr1
  refine ⟨(s1 : ℤ) - (s0 : ℤ), (t1 : ℤ) - (t0 : ℤ), ?_⟩
  linarith
