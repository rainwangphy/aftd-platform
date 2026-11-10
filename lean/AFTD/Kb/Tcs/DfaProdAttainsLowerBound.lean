import AFTD.Prelude
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaProd

/-!
# dfa_prod_attains_lower_bound

Topic: automata   Node: fdef84abea9f

Provenance: formalization of a published result. Source: arXiv:2611.09136 Sec. 7, open question 1

A pair of DFAs `A₁` and `A₂` over the same alphabet attains the lower bound of Proposition 3.4 if the reset threshold of their direct product equals `max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂)`.
-/

/-- Predicate asserting that the reset threshold of `dfa_prod A₁ A₂` attains the lower bound `max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂)`. -/
def dfa_prod_attains_lower_bound {α σ₁ σ₂ : Type*} (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) : Prop := dfa_reset_threshold (dfa_prod A₁ A₂) = max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂)
