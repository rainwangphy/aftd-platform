import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstSolves
import AFTD.Kb.Tcs.StochasticMstSolvesAux
import AFTD.Kb.Tcs.StochasticMstQueryEligible
import AFTD.Kb.Tcs.StochasticMstStrategy

/-!
# stochastic_mst_query_continuation_solves

Topic: algorithms   Node: bb5d9e0a852e

Provenance: formalization of a published result. Source: arXiv:2610.40844 Lemma 3.1

For a graph G and an edge e that is query-eligible at the initial state (∅, ∅), the strategy querying e with children s₀ and s₁ solves the adaptive MST identification problem for G if and only if s₀ solves the subproblem from state ({e}, ∅) and s₁ solves the subproblem from state (∅, {e}).
-/

/-- Lemma 3.1: Querying an eligible edge e and following s₀ on 0 and s₁ on 1 solves MST-ID iff s₀ and s₁ solve the contracted and deleted subproblems. -/
theorem stochastic_mst_query_continuation_solves {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (e : Sym2 V) (s₀ s₁ : StochasticMstStrategy (Sym2 V))
    (he : stochastic_mst_query_eligible G ∅ ∅ e) :
    stochastic_mst_solves G (StochasticMstStrategy.query e s₀ s₁) ↔
      stochastic_mst_solves_aux G {e} ∅ s₀ ∧ stochastic_mst_solves_aux G ∅ {e} s₁ := by
  rw [stochastic_mst_solves, stochastic_mst_solves_aux.eq_2]
  simp [he.1]
