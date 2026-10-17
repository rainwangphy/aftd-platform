import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset

/-!
# int_mem_h_fold_sumset_of_list

Topic: elementary_number_theory   Node: 3baaf7553eef

Provenance: helper lemma. Helper for h-fold sumsets (arXiv:2610.19470 (Positivity and negativity for h-bases for n)), serving postage_stamp_basis_range_eight_neg_four_one_thirteen_fourteen.

The sum of a list of h elements of A lies in hA.
-/

theorem int_mem_h_fold_sumset_of_list (A : Finset ℤ) (l : List ℤ) (hA : ∀ x ∈ l, x ∈ A) :
    int_mem_h_fold_sumset l.length A l.sum := by
  refine ⟨fun i => l.get i, fun i => hA _ (List.get_mem l i), ?_⟩
  simpa using (List.sum_ofFn (f := fun i => l.get i)).symm.trans (by rw [List.ofFn_get])
