import AFTD.Prelude

/-!
# normal_form_expected_payoff

Topic: equilibria   Node: 7c7900e7a39c

Provenance: formalization of a published result. Source: arXiv:2611.06076 Section 2

In an n-player normal-form game with action types A : Fin n → Type, finite action spaces, and payoff function u : Fin n → ((j : Fin n) → A j) → ℝ, the expected payoff to player i : Fin n under a profile of probability distributions x : (j : Fin n) → stdSimplex ℝ (A j) is the sum over pure action profiles a : (j : Fin n) → A j of (∏ j : Fin n, (x j).val (a j)) * u i a.
-/

/-- Expected payoff to player i in a finite normal-form game under a product mixed profile. -/
def normal_form_expected_payoff {n : ℕ} {A : Fin n → Type} [∀ i, Fintype (A i)]
    (u : Fin n → ((i : Fin n) → A i) → ℝ) (i : Fin n)
    (x : (j : Fin n) → stdSimplex ℝ (A j)) : ℝ :=
  ∑ a : (j : Fin n) → A j, (∏ j, (x j).val (a j)) * u i a
