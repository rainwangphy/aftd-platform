import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteSubsetStandardListColorable

/-!
# bipartite_subset_min_uncolorable_r

Topic: graphs   Node: d35e87dff9d5

Provenance: formalization of a published result. Source: arXiv:2610.42094, after Corollary 1.4

For an integer k, bipartite_subset_min_uncolorable_r k is the least nonnegative integer r such that bipartite_subset_graph k r has no proper coloring from its standard lists, defined as the infimum (sInf) of the set of natural numbers r such that ¬ bipartite_subset_standard_list_colorable k r.
-/

/-- The least integer r ≥ 0 such that G(k,r) has no proper coloring from standard lists. -/
noncomputable def bipartite_subset_min_uncolorable_r (k : ℕ) : ℕ := sInf {r : ℕ | ¬ bipartite_subset_standard_list_colorable k r}
