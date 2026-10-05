import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGame

/-!
# agCyc

Topic: equilibria   Node: 36565073a4b4

The cyclic game u_i(y) = (y_{i+1} + min(y_i, 2)) / 4: a player on strategy i gains from others on the "next" strategy i+1 and from company on its own strategy (up to two).
-/

/-- The cyclic game `u_i(y) = (y_{i+1} + min(y_i, 2)) / 4`: a player on strategy `i` gains from others on the "next" strategy `i+1` and from company on its own strategy (up to two). -/
def agCyc (n s : ℕ) [NeZero s] : AGGame n s where
  u _ i y := ((y (i + 1) : ℚ) + min (y i : ℚ) 2) / 4
