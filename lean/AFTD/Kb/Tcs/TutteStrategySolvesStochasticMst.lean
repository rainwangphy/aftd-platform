import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstIsTutte
import AFTD.Kb.Tcs.StochasticMstSolves
import AFTD.Kb.Tcs.StochasticMstStrategy
import AFTD.Kb.Tcs.StochasticMstIsTutteAux
import AFTD.Kb.Tcs.StochasticMstSolvesAux
import AFTD.Kb.Tcs.StochasticMstQueryEligible

/-!
# tutte_strategy_solves_stochastic_mst

Topic: algorithms   Node: 43e90d82a3fa

Provenance: formalization of a published result. Source: arXiv:2610.40844 Lemma 3.3

For any graph G, every Tutte strategy T for G solves the adaptive MST identification problem for G.
-/

/-- From any state (Z, D), a Tutte strategy for G solves the adaptive MST identification problem. -/
theorem tutte_strategy_solves_stochastic_mst_aux {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    ∀ (T : StochasticMstStrategy (Sym2 V)) (Z D : Finset (Sym2 V)),
      stochastic_mst_is_tutte_aux G Z D T → stochastic_mst_solves_aux G Z D T := by
  intro T
  induction T with
  | leaf =>
    intro Z D h
    rw [stochastic_mst_solves_aux.eq_def]
    exact h
  | query e s0 s1 ih0 ih1 =>
    intro Z D h
    rw [stochastic_mst_is_tutte_aux.eq_def] at h
    rw [stochastic_mst_solves_aux.eq_def]
    exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, ih0 (insert e Z) D h.2.1, ih1 Z (insert e D) h.2.2⟩

/-- Lemma 3.3: Every Tutte strategy for G solves the adaptive MST identification problem for G. -/
theorem tutte_strategy_solves_stochastic_mst {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (T : StochasticMstStrategy (Sym2 V)) (hT : stochastic_mst_is_tutte G T) :
    stochastic_mst_solves G T := by
  exact tutte_strategy_solves_stochastic_mst_aux G T ∅ ∅ hT
