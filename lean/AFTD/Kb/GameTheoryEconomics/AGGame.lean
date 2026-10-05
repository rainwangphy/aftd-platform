import AFTD.Prelude

/-!
# AGGame

Topic: equilibria   Node: 626007a3e94c

An anonymous game with n players and s strategies (setting of arXiv 0710.5582, "Computing equilibria in anonymous games", Section 2): the payoff of player p for strategy i depends only on the vector y : Fin s → ℕ of counts of the *other* players on each strategy.
-/

/-- An anonymous game with `n` players and `s` strategies (setting of arXiv 0710.5582, "Computing equilibria in anonymous games", Section 2): the payoff of player `p` for strategy `i` depends only on the vector `y : Fin s → ℕ` of counts of the *other* players on each strategy. -/
structure AGGame (n s : ℕ) where
  u : Fin n → Fin s → (Fin s → ℕ) → ℚ
