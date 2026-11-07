import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstSolvesAux
import AFTD.Kb.Tcs.StochasticMstStrategy

/-!
# stochastic_mst_solves

Topic: algorithms   Node: 27c20547ed50

Provenance: formalization of a published result. Source: arXiv:2610.40844 Sections 2.1 & 3

A strategy T solves the adaptive MST identification problem for G if it solves the problem starting from the empty state of contracted and deleted edges.
-/

/-- A strategy solves the adaptive MST identification problem for G if it solves it starting from (∅, ∅). -/
def stochastic_mst_solves {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (T : StochasticMstStrategy (Sym2 V)) : Prop := stochastic_mst_solves_aux G ∅ ∅ T
