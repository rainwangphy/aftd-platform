import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset

/-!
# postage_stamp_number_neg_two_of_odd_cons

Topic: elementary_number_theory   Node: 9262a5640ca9

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

Adding an element of A to an element of hA gives an element of (h+1)A.
-/

theorem postage_stamp_number_neg_two_of_odd_cons (k : ℕ) (A : Finset ℤ)
    (n a : ℤ) (hn : int_mem_h_fold_sumset k A n) (ha : a ∈ A) :
    int_mem_h_fold_sumset (k + 1) A (a + n) := by
  obtain ⟨f, hf, hs⟩ := hn
  refine ⟨Fin.cons a f, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using hf j
  · rw [Fin.sum_univ_succ]
    simp [hs]
