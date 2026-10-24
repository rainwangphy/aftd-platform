import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_number_neg_two_of_odd_range_ge

Topic: elementary_number_theory   Node: 69bdad0086c3

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

If A is bounded above and h-fold covers [0, R], its h-range is at least R.
-/

theorem postage_stamp_number_neg_two_of_odd_range_ge (h R : ℕ) (A : Finset ℤ) (B : ℤ) (hB : ∀ a ∈ A, a ≤ B)
    (hcov : ∀ n : ℕ, n ≤ R → int_mem_h_fold_sumset h A n) :
    R ≤ postage_stamp_basis_range h A := by
  have hbdd : BddAbove {n : ℕ | ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset h A m} := by
    refine ⟨((h : ℤ) * B).toNat, fun n hn => ?_⟩
    obtain ⟨f, hf, hs⟩ := hn n le_rfl
    have : (n : ℤ) ≤ (h : ℤ) * B := by
      rw [← hs]
      calc ∑ i, f i ≤ ∑ _i : Fin h, B := Finset.sum_le_sum (fun i _ => hB _ (hf i))
        _ = _ := by simp
    have := Int.self_le_toNat ((h : ℤ) * B)
    omega
  exact le_csSup hbdd hcov
