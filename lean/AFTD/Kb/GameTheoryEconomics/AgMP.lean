import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGame

/-!
# agMP

Topic: equilibria   Node: 08f0ca380ac7

Matching pennies as a 2-player, 2-strategy anonymous game: player 0 wants to match the other player, player 1 wants to mismatch.
-/

/-- Matching pennies as a 2-player, 2-strategy anonymous game: player `0` wants to match the other player, player `1` wants to mismatch. -/
def agMP : AGGame 2 2 where
  u p i y := if p = 0 then (if y i = 1 then 1 else 0) else (if y i = 0 then 1 else 0)
