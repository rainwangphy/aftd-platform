import AFTD.Prelude

/-!
# agCycV

Topic: equilibria   Node: 4261ca5f43ed

Integer numerator of the cyclic game's payoff.
-/

/-- Integer numerator of the cyclic game's payoff. -/
def agCycV {s : ℕ} [NeZero s] (i : Fin s) (y : Fin s → ℕ) : ℕ := y (i + 1) + min (y i) 2
