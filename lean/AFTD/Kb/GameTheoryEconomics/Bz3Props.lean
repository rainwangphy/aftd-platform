import AFTD.Prelude

/-!
# bz3_props

Topic: general_equilibrium   Node: 141318a3ee56

Necessary conditions on the winning pattern of a 3-player weighted game with simplex weights and strict quota 1/2: empty loses, grand coalition wins, monotone, no coalition wins together with its complement.
-/

/-- Necessary conditions on the winning coalitions of a 3-player weighted game with weights in the simplex and strict quota 1/2: the empty coalition loses, the grand coalition wins, winning is monotone, and a coalition and its complement cannot both win. -/
def bz3_props (x : Fin 8 → Bool) : Bool :=
  !x 0 && x 7 &&
  (!x 0 || x 1) && (!x 0 || x 2) && (!x 0 || x 4) && (!x 1 || x 3) && (!x 1 || x 5) &&
  (!x 2 || x 3) && (!x 2 || x 6) && (!x 4 || x 5) && (!x 4 || x 6) && (!x 3 || x 7) &&
  (!x 5 || x 7) && (!x 6 || x 7) &&
  (!x 1 || !x 6) && (!x 2 || !x 5) && (!x 4 || !x 3)
