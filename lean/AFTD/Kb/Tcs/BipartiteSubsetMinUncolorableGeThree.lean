import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteSubsetMinUncolorableR
import AFTD.Kb.Tcs.BipartiteSubsetColorableIffBelowThreshold
import AFTD.Kb.Tcs.BipartiteSubsetColorableTwoFromFive
import AFTD.Kb.Tcs.BipartiteSubsetStandardListColorable

/-!
# bipartite_subset_min_uncolorable_ge_three

Topic: graphs   Node: 1da5fcfc8293

Provenance: helper lemma. A direct consequence of the list-coloring construction for OP-861, arXiv:2610.42094.

For every k at least 5, the least uncolorable threshold is at least 3.
-/

theorem bipartite_subset_min_uncolorable_ge_three (k : ℕ) (hk : 5 ≤ k) : 3 ≤ bipartite_subset_min_uncolorable_r k := by
  have h := (bipartite_subset_colorable_iff_below_threshold k 2 (by omega)).1 (bipartite_subset_colorable_two_from_five k hk)
  omega
