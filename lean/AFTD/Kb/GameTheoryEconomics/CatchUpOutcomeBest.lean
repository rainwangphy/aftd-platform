import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# CatchUpOutcome.best

Topic: combinatorial_games   Node: 6865fe2df38b

Given a list of outcomes, the best one for the player who chooses, under the order win > draw > loss (and loss if the list is empty).
-/

/-- The best outcome in a list for the player choosing among them, ordering win > draw > loss; `loss` for the empty list. -/
def CatchUpOutcome.best (os : List CatchUpOutcome) : CatchUpOutcome :=
  os.foldl (fun
    | .win,  _     => .win
    | _,     .win  => .win
    | .draw, _     => .draw
    | _,     .draw => .draw
    | _,     _     => .loss) .loss
