import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value

Topic: combinatorial_games   Node: 968805cf677f

The outcome of Catch-Up played on the finite set S of natural numbers, from the first player's point of view, assuming optimal play by both players.
-/

/-- The value of Catch-Up on the set `S` for the first player, under optimal play, both scores starting at 0. -/
noncomputable def catch_up_value (S : Finset ℕ) : CatchUpOutcome :=
  catch_up_value_aux S 0 0 true
