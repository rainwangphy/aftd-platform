import AFTD.Prelude

/-!
# CatchUpOutcome

Topic: combinatorial_games   Node: 073e6712ac4e

The three possible outcomes of a game of Catch-Up, from the point of view of a fixed player: win, loss, draw.
-/

/-- The outcome of a game of Catch-Up from one player's point of view: win, loss or draw. -/
inductive CatchUpOutcome where
  | win
  | loss
  | draw
deriving DecidableEq, Repr
