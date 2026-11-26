import AFTD.Prelude
import AFTD.Kb.Tcs.GndMarginalCost
import AFTD.Kb.Tcs.GndPartialLoad

/-!
# is_tau_approx_greedy

Topic: online_algorithms   Node: f17c6f511c2b

Provenance: formalization of a published result. Source: arXiv:2611.30912 Section 2

An online reply sequence alg_reply is tau-approximately greedy if each alg_reply i is feasible (alg_reply i ∈ replies i) and its marginal cost increase at step i is at most tau times the marginal cost increase of any other feasible reply R ∈ replies i.
-/

/-- Predicate asserting that an online sequence of replies is tau-approximately greedy with respect to marginal cost increase. -/
def is_tau_approx_greedy {E : Type*} [DecidableEq E] {N : ℕ}
    (c : E → ℝ) (pe : E → ℝ) (w : Fin N → E → ℝ)
    (replies : Fin N → Set (Finset E))
    (alg_reply : Fin N → Finset E) (τ : ℝ) : Prop := (∀ i : Fin N, alg_reply i ∈ replies i) ∧
  (∀ (i : Fin N) (R : Finset E), R ∈ replies i →
    gnd_marginal_cost c pe (gnd_partial_load alg_reply w i) (w i) (alg_reply i) ≤
      τ * gnd_marginal_cost c pe (gnd_partial_load alg_reply w i) (w i) R)
