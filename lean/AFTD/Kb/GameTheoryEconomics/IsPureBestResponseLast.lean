import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NormalFormExpectedPayoff
import AFTD.Kb.Optimization.StdSimplexPure

/-!
# is_pure_best_response_last

Topic: equilibria   Node: 7ded3f3bbda2

Provenance: formalization of a published result. Source: arXiv:2611.06076 Lemma 2.1

In an (r+1)-player game with payoff function u : Fin (r + 1) → ((j : Fin (r + 1)) → A j) → ℝ and action types A, pure action b : A (Fin.last r) is a pure best response for player Fin.last r against mixed profile x : (j : Fin r) → stdSimplex ℝ (A j.castSucc) if for every pure action a : A (Fin.last r), the expected payoff to player Fin.last r under Fin.snoc x (stdSimplex.pure a) is at most that under Fin.snoc x (stdSimplex.pure b).
-/

/-- Pure best response for the last player against a profile of the other players. -/
def is_pure_best_response_last {r : ℕ} {A : Fin (r + 1) → Type}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (u : Fin (r + 1) → ((i : Fin (r + 1)) → A i) → ℝ)
    (x : (j : Fin r) → stdSimplex ℝ (A j.castSucc))
    (b : A (Fin.last r)) : Prop :=
  ∀ a : A (Fin.last r),
    normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure a)) ≤
      normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure b))
