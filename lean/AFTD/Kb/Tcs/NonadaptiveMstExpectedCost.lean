import AFTD.Prelude
import AFTD.Kb.Tcs.RealizationProb
import AFTD.Kb.Tcs.NonadaptiveMstStoppingTime

/-!
# nonadaptive_mst_expected_cost

Topic: approximation   Node: b7458149cc78

Provenance: formalization of a published result. Source: arXiv:2610.40844 Sec. 6.3

The expected query cost of a non-adaptive querying order π on a finite graph G with decidable adjacency and edge probabilities p is the sum over all binary edge realizations α of the product Bernoulli probability of α times the stopping time of π on α.
-/

/-- The expected query cost of a non-adaptive querying order π under edge probabilities p. -/
noncomputable def nonadaptive_mst_expected_cost {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : G.edgeSet → ℝ) (π : List G.edgeSet) : ℝ := ∑ α : G.edgeSet → Bool, (realization_prob G p α) * (nonadaptive_mst_stopping_time G π α : ℝ)
