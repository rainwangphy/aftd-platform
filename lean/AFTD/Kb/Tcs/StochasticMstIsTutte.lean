import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstIsTutteAux
import AFTD.Kb.Tcs.StochasticMstStrategy

/-!
# stochastic_mst_is_tutte

Topic: algorithms   Node: 59d25a9247dd

Provenance: formalization of a published result. Source: arXiv:2610.40844 Section 3

A strategy T is a Tutte strategy for G if it satisfies the Tutte strategy predicate starting from the empty state of contracted and deleted edges.
-/

/-- A Tutte strategy for graph G is a binary decision tree whose root starts at the empty state (∅, ∅). -/
def stochastic_mst_is_tutte {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (T : StochasticMstStrategy (Sym2 V)) : Prop := stochastic_mst_is_tutte_aux G ∅ ∅ T
