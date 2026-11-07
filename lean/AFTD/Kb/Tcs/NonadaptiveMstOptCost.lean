import AFTD.Prelude
import AFTD.Kb.Tcs.NonadaptiveMstExpectedCost

/-!
# nonadaptive_mst_opt_cost

Topic: approximation   Node: 3baedb85004d

Provenance: formalization of a published result. Source: arXiv:2610.40844 Sec. 6.3

The optimal non-adaptive expected query cost on a finite graph G with decidable adjacency and edge probabilities p is the infimum of the expected query cost over all permutations π of the edge set of G.
-/

/-- The optimal expected query cost among all permutations of edges of G. -/
noncomputable def nonadaptive_mst_opt_cost {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : G.edgeSet → ℝ) : ℝ := sInf {c : ℝ | ∃ π : List G.edgeSet, π.Perm (Finset.univ : Finset G.edgeSet).toList ∧ c = nonadaptive_mst_expected_cost G p π}
