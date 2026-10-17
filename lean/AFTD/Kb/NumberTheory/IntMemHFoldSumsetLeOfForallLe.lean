import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# int_mem_h_fold_sumset_le_of_forall_le

Topic: elementary_number_theory   Node: d196c3de9a89

Provenance: helper lemma. Helper for h-fold sumsets (arXiv:2610.19470 (Positivity and negativity for h-bases for n)): the boundedness that makes n_h(A) a maximum.

If every element of A is at most b, every element of hA is at most h·b.
-/

theorem int_mem_h_fold_sumset_le_of_forall_le (h : ℕ) (A : Finset ℤ) (b : ℤ) (hb : ∀ a ∈ A, a ≤ b)
    (m : ℤ) (hm : int_mem_h_fold_sumset h A m) : m ≤ h * b := by
  obtain ⟨f, hf, rfl⟩ := hm
  calc ∑ i, f i ≤ ∑ _i : Fin h, b := Finset.sum_le_sum fun i _ => hb _ (hf i)
    _ = h * b := by simp
