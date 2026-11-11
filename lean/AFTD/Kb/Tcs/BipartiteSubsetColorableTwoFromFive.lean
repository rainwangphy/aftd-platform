import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteSubsetStandardListColorable
import AFTD.Kb.Tcs.BipartiteSubsetColorableFiveAtTwo
import AFTD.Kb.Tcs.BipartiteSubsetColorableSucc

/-!
# bipartite_subset_colorable_two_from_five

Topic: graphs   Node: ad9c73880867

Provenance: original. Related work: A constant-threshold partial result toward OP-861 in arXiv:2610.42094; compare its upper bound on the least uncolorable threshold.

For every k at least 5, the bipartite subset graph with intersection threshold 2 is colorable from its standard lists.
-/

theorem bipartite_subset_colorable_two_from_five (k : ℕ) (hk : 5 ≤ k) : bipartite_subset_standard_list_colorable k 2 := by
  induction k, hk using Nat.le_induction with
  | base => exact bipartite_subset_colorable_five_at_two
  | succ k hk ih => exact bipartite_subset_colorable_succ k 2 (by omega) ih
