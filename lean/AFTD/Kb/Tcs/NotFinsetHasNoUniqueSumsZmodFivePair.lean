import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount

/-!
# not_finset_has_no_unique_sums_zmod_five_pair

Topic: combinatorics   Node: 73026819d3c0

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.09349 on a small case.

The set {0, 1} in Z/5Z has unique sums (0 + 0 has only one representation).
-/

theorem not_finset_has_no_unique_sums_zmod_five_pair :
    ¬ finset_has_no_unique_sums ({0, 1} : Finset (ZMod 5)) := by
  unfold finset_has_no_unique_sums finset_unordered_sum_rep_count; decide
