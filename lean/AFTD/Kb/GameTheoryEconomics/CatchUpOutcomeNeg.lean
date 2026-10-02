import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# CatchUpOutcome.neg

Topic: combinatorial_games   Node: 2e6e48421c57

Negation of an outcome: win and loss are exchanged, draw is fixed. Used when the turn passes to the other player.
-/

/-- Swap the point of view: a win for one player is a loss for the other; a draw stays a draw. -/
def CatchUpOutcome.neg : CatchUpOutcome → CatchUpOutcome := fun
  | .win => .loss
  | .loss => .win
  | .draw => .draw
