import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NormalFormExpectedPayoff
import AFTD.Kb.Optimization.StdSimplexPure

/-!
# is_approx_nash_equilibrium

Topic: equilibria   Node: 10543a80fbda

Provenance: formalization of a published result. Source: arXiv:2611.06076 Section 2

A strategy profile x : (j : Fin n) → stdSimplex ℝ (A j) in an n-player normal-form game with payoff function u : Fin n → ((j : Fin n) → A j) → ℝ is an ε-approximate Nash equilibrium if for every player i : Fin n and every pure action a : A i, the expected payoff under Function.update x i (stdSimplex.pure a) minus the expected payoff under x is at most ε.
-/

/-- An ε-approximate Nash equilibrium has regret at most ε for every player. -/
def is_approx_nash_equilibrium {n : ℕ} {A : Fin n → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (u : Fin n → ((i : Fin n) → A i) → ℝ) (ε : ℝ)
    (x : (j : Fin n) → stdSimplex ℝ (A j)) : Prop :=
  ∀ (i : Fin n) (a : A i),
    normal_form_expected_payoff u i (Function.update x i (stdSimplex.pure a)) -
      normal_form_expected_payoff u i x ≤ ε
