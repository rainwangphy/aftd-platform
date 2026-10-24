import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddMemOfSt

/-!
# postage_stamp_number_neg_two_of_odd_rep_e

Topic: elementary_number_theory   Node: c9a7257c7e31

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

For h = 12r+5 and the set {-(2r+1), 2r+1, 4r+4}: (2r+1)D + (4r+4)t is an h-fold sum whenever 0 ≤ t, |D| ≤ h - t and h - t - D is even.
-/

theorem postage_stamp_number_neg_two_of_odd_rep_e (r : ℕ) (t D : ℤ) (ht0 : 0 ≤ t)
    (hD1 : -((12 * (r : ℤ) + 5) - t) ≤ D) (hD2 : D ≤ (12 * (r : ℤ) + 5) - t)
    (hpar : ((12 * (r : ℤ) + 5) - t - D) % 2 = 0) :
    int_mem_h_fold_sumset (12 * r + 5) {-(2 * (r : ℤ) + 1), 2 * (r : ℤ) + 1, 4 * (r : ℤ) + 4}
      ((2 * (r : ℤ) + 1) * D + (4 * (r : ℤ) + 4) * t) := by
  set e : ℤ := ((12 * (r : ℤ) + 5) - t - D) / 2 with he
  have he2 : 2 * e = (12 * (r : ℤ) + 5) - t - D := by omega
  have hs := postage_stamp_number_neg_two_of_odd_mem_of_st (12 * r + 5) (-(2 * (r : ℤ) + 1)) (2 * (r : ℤ) + 1) (4 * (r : ℤ) + 4)
    (e + D).toNat t.toNat (by omega)
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg ht0] at hs
  have hv : (2 * (r : ℤ) + 1) * D + (4 * (r : ℤ) + 4) * t =
      ((12 * r + 5 : ℕ) : ℤ) * (-(2 * (r : ℤ) + 1)) + (e + D) * ((2 * (r : ℤ) + 1) - (-(2 * (r : ℤ) + 1))) +
        t * ((4 * (r : ℤ) + 4) - (-(2 * (r : ℤ) + 1))) := by
    push_cast; linear_combination (-(2 * (r : ℤ) + 1)) * he2
  rw [hv]; exact hs
