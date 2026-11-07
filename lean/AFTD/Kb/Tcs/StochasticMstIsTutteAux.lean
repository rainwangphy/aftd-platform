import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstStrategy
import AFTD.Kb.Tcs.StochasticMstQueryEligible

/-!
# stochastic_mst_is_tutte_aux

Topic: algorithms   Node: cadf38e4434b

Provenance: formalization of a published result. Source: arXiv:2610.40844 Section 3

From state (Z, D) of contracted edges Z and deleted edges D, a strategy is a Tutte strategy for G if at a leaf no edge of G is query-eligible (every remaining edge of the minor is a loop or bridge), and at an internal query on e, e is query-eligible at (Z, D), the 0-child is a Tutte strategy from (insert e Z, D), and the 1-child is a Tutte strategy from (Z, insert e D).
-/

/-- Predicate stating that a strategy is a Tutte strategy from state (Z, D) of contracted and deleted edges. -/
def stochastic_mst_is_tutte_aux {V : Type*} [DecidableEq V] (G : SimpleGraph V) (Z D : Finset (Sym2 V)) :
    StochasticMstStrategy (Sym2 V) → Prop
| StochasticMstStrategy.leaf => ∀ e, ¬ stochastic_mst_query_eligible G Z D e
| StochasticMstStrategy.query e s₀ s₁ =>
    stochastic_mst_query_eligible G Z D e ∧
    stochastic_mst_is_tutte_aux G (insert e Z) D s₀ ∧
    stochastic_mst_is_tutte_aux G Z (insert e D) s₁
