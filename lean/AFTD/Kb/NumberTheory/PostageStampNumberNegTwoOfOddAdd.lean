import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddCons

/-!
# postage_stamp_number_neg_two_of_odd_add

Topic: elementary_number_theory   Node: ccdc3784bb29

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

Adding c copies of an element s of A to an element of kA gives an element of (k+c)A.
-/

theorem postage_stamp_number_neg_two_of_odd_add (A : Finset ℤ) (s : ℤ)
    (hs : s ∈ A) (k : ℕ) (n : ℤ) (hn : int_mem_h_fold_sumset k A n) :
    ∀ c : ℕ, int_mem_h_fold_sumset (k + c) A (n + c * s) := by
  intro c
  induction c with
  | zero => simpa using hn
  | succ c ih =>
    have := postage_stamp_number_neg_two_of_odd_cons (k + c) A _ s ih hs
    have e : s + (n + (c : ℤ) * s) = n + ((c + 1 : ℕ) : ℤ) * s := by push_cast; ring
    rw [e] at this
    rw [show k + (c + 1) = k + c + 1 by omega]
    exact this
