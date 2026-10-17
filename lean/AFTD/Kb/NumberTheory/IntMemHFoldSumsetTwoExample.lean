import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset

/-!
# int_mem_h_fold_sumset_two_example

Topic: elementary_number_theory   Node: 0a100a44411e

Provenance: helper lemma. Sanity lemma for h-fold sumsets, arXiv:2610.19470 (Positivity and negativity for h-bases for n).

Sanity check: 4 = 1 + 3 lies in 2{0, 1, 3}.
-/

theorem int_mem_h_fold_sumset_two_example : int_mem_h_fold_sumset 2 {0, 1, 3} 4 :=
  ⟨![1, 3], by decide, by simp⟩
