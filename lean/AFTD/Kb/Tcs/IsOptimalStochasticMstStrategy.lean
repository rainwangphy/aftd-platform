import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstSolves
import AFTD.Kb.Tcs.StochasticMstStrategyCost
import AFTD.Kb.Tcs.StochasticMstStrategy

/-!
# is_optimal_stochastic_mst_strategy

Topic: algorithms   Node: 159aae9023e1

Provenance: formalization of a published result. Source: arXiv:2610.40844 Section 2.1 & Lemma 3.2

A strategy T is an optimal strategy solving the adaptive MST identification problem for graph G with edge probabilities p if T solves the MST-ID problem for G and for every strategy T' that solves the MST-ID problem for G, the expected cost of T under p is at most the expected cost of T' under p.
-/

/-- A strategy is optimal for an instance (G, p) if it solves MST-ID and minimizes expected cost. -/
def is_optimal_stochastic_mst_strategy {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (p : Sym2 V → ℝ) (T : StochasticMstStrategy (Sym2 V)) : Prop := stochastic_mst_solves G T ∧
  ∀ T' : StochasticMstStrategy (Sym2 V), stochastic_mst_solves G T' →
    stochastic_mst_strategy_cost p T ≤ stochastic_mst_strategy_cost p T'
