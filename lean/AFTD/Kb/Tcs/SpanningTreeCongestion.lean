import AFTD.Prelude
import AFTD.Kb.Tcs.FundamentalCutLoad

/-!
# spanning_tree_congestion

Topic: approximation   Node: 7830e821259c

Provenance: helper lemma. step towards weighted_spanning_tree_congestion_hardness_gap

The weighted spanning tree congestion of a graph `H` with edge weights `w` is the infimum, over all spanning trees `T` of `H`, of the maximum load of a fundamental cut of `T`.
-/

/-- Weighted spanning tree congestion `STC_w(H)`: the infimum of the maximum fundamental-cut load over all spanning trees of `H`, as a natural number. -/
noncomputable def spanning_tree_congestion {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj] (w : Sym2 α → ℕ) : ℕ := by
  classical
  exact sInf {c : ℕ | ∃ T : SimpleGraph α,
    T ≤ H ∧ T.IsTree ∧ T.edgeFinset.sup (fundamental_cut_load H w T) = c}
