import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetIsMidpointBalanced

/-!
# finset_is_midpoint_balanced_univ_zmod_three

Topic: combinatorics   Node: 5c0cd5c489ab

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.09349 on a small case.

Z/3Z is balanced: each element is the midpoint of the other two.
-/

theorem finset_is_midpoint_balanced_univ_zmod_three :
    finset_is_midpoint_balanced (Finset.univ : Finset (ZMod 3)) := by
  unfold finset_is_midpoint_balanced; decide
