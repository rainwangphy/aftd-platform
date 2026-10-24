import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddAdd
import AFTD.Kb.NumberTheory.IntMemHFoldSumset

/-!
# postage_stamp_number_neg_two_of_odd_mem_of_st

Topic: elementary_number_theory   Node: 88bcf56b9d60

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

For s + t ≤ h, h·a + s(b-a) + t(c-a) lies in the h-fold sumset of {a, b, c}.
-/

theorem postage_stamp_number_neg_two_of_odd_mem_of_st (h : ℕ) (a b c : ℤ) (s t : ℕ) (hst : s + t ≤ h) :
    int_mem_h_fold_sumset h {a, b, c} ((h : ℤ) * a + (s : ℤ) * (b - a) + (t : ℤ) * (c - a)) := by
  have h0 : int_mem_h_fold_sumset 0 ({a, b, c} : Finset ℤ) 0 :=
    ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  have h1 := postage_stamp_number_neg_two_of_odd_add {a, b, c} a (by simp) 0 0 h0 (h - s - t)
  have h2 := postage_stamp_number_neg_two_of_odd_add {a, b, c} b (by simp) _ _ h1 s
  have h3 := postage_stamp_number_neg_two_of_odd_add {a, b, c} c (by simp) _ _ h2 t
  rw [show 0 + (h - s - t) + s + t = h by omega] at h3
  have e : (0 : ℤ) + ((h - s - t : ℕ) : ℤ) * a + (s : ℤ) * b + (t : ℤ) * c =
      (h : ℤ) * a + (s : ℤ) * (b - a) + (t : ℤ) * (c - a) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
  rw [e] at h3
  exact h3
