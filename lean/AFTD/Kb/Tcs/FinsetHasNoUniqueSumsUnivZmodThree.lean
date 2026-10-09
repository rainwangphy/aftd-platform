import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount

/-!
# finset_has_no_unique_sums_univ_zmod_three

Topic: combinatorics   Node: 4c1b79939c8b

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.09349 on a small case. The paper notes that F_p itself is NUS (Sec. 1).

The whole of Z/3Z has no unique sums.
-/

theorem finset_has_no_unique_sums_univ_zmod_three :
    finset_has_no_unique_sums (Finset.univ : Finset (ZMod 3)) := by
  unfold finset_has_no_unique_sums finset_unordered_sum_rep_count; decide
