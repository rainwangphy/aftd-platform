import AFTD.Prelude

/-!
# normal_form_subgame_last

Topic: equilibria   Node: af66fdeafefa

Provenance: formalization of a published result. Source: arXiv:2611.06076 Lemma 2.1

Given action types A : Fin (r + 1) → Type and payoff function u : Fin (r + 1) → ((j : Fin (r + 1)) → A j) → ℝ for an (r+1)-player game, the r-player subgame payoff function obtained by fixing player Fin.last r to pure action s : A (Fin.last r) assigns to each player i : Fin r and action profile a : (j : Fin r) → A j.castSucc the payoff u i.castSucc (Fin.snoc a s).
-/

/-- Subgame obtained by fixing the last player's pure action. -/
def normal_form_subgame_last {r : ℕ} {A : Fin (r + 1) → Type}
    (u : Fin (r + 1) → ((i : Fin (r + 1)) → A i) → ℝ) (s : A (Fin.last r)) :
    Fin r → ((i : Fin r) → A i.castSucc) → ℝ :=
  fun i a => u i.castSucc (Fin.snoc a s)
