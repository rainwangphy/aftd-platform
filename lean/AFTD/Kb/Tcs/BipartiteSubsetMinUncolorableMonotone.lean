import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteSubsetMinUncolorableR
import AFTD.Kb.Tcs.BipartiteSubsetColorableIffBelowThreshold
import AFTD.Kb.Tcs.BipartiteSubsetColorableSucc
import AFTD.Kb.Tcs.BipartiteSubsetStandardListColorable

/-!
# bipartite_subset_min_uncolorable_monotone

Topic: graphs   Node: 27066bca4692

Provenance: helper lemma. A direct consequence of the list-coloring construction for OP-861, arXiv:2610.42094.

For positive k, the least uncolorable threshold is nondecreasing as k increases.
-/

theorem bipartite_subset_min_uncolorable_monotone (k : ℕ) (hk : 1 ≤ k) : bipartite_subset_min_uncolorable_r k ≤ bipartite_subset_min_uncolorable_r (k+1) := by
  by_contra! h
  let r := bipartite_subset_min_uncolorable_r (k+1)
  have hc : bipartite_subset_standard_list_colorable k r := (bipartite_subset_colorable_iff_below_threshold k r hk).2 h
  have hcnew := bipartite_subset_colorable_succ k r hk hc
  have hh := (bipartite_subset_colorable_iff_below_threshold (k+1) r (by omega)).1 hcnew
  omega
