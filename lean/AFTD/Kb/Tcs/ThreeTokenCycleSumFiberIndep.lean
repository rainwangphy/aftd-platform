import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.ThreeTokenCycleAdjSumDiff

/-!
# three_token_cycle_sum_fiber_indep

Topic: graphs   Node: 19f4c43416c0

Provenance: helper lemma. arXiv:2611.22830 Section 5; open problem OP-2010

For any natural number n ≥ 3 and any subset S of ZMod n with no two elements differing by 1, the set of 3-element subsets of Fin n whose coordinate sum in ZMod n belongs to S is an independent set in the 3-token graph of C_n.
-/

/-- A set of residues without consecutive elements pulls back to an independent set in the 3-token graph of C_n. -/
theorem three_token_cycle_sum_fiber_indep (n : ℕ) (hn : 3 ≤ n)
    (S : Set (ZMod n))
    (hS : ∀ a ∈ S, ∀ b ∈ S, ¬ (a - b = 1 ∨ b - a = 1)) :
    (token_graph (SimpleGraph.cycleGraph n) 3).IsIndepSet
      { x | x.val.sum (fun i => (i : ZMod n)) ∈ S } := by
  intro x hx y hy hne hadj
  have hdiff := three_token_cycle_adj_sum_diff n hn x y hadj
  exact hS _ hx _ hy hdiff
