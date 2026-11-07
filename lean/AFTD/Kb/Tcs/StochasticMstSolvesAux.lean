import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstStrategy
import AFTD.Kb.Tcs.StochasticMstQueryEligible

/-!
# stochastic_mst_solves_aux

Topic: algorithms   Node: 7675cdba8d57

Provenance: formalization of a published result. Source: arXiv:2610.40844 Sections 2.1 & 3

From state (Z, D) of contracted edges Z and deleted edges D, a strategy solves the adaptive MST identification problem for G if at every leaf no edge of G is query-eligible (all remaining edges of the minor are loops or bridges, certifying an MST), and each internal node queries an unqueried edge of G with its 0-child and 1-child solving the subproblems after contracting and deleting e, respectively.
-/

/-- Predicate stating that a strategy solves the adaptive MST identification problem for G from state (Z, D). -/
def stochastic_mst_solves_aux {V : Type*} [DecidableEq V] (G : SimpleGraph V) (Z D : Finset (Sym2 V)) :
    StochasticMstStrategy (Sym2 V) → Prop
| StochasticMstStrategy.leaf => ∀ e, ¬ stochastic_mst_query_eligible G Z D e
| StochasticMstStrategy.query e s₀ s₁ =>
    e ∈ G.edgeSet ∧ e ∉ Z ∧ e ∉ D ∧
    stochastic_mst_solves_aux G (insert e Z) D s₀ ∧
    stochastic_mst_solves_aux G Z (insert e D) s₁
