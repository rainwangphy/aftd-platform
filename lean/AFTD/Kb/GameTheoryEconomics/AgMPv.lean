import AFTD.Prelude

/-!
# agMPv

Topic: equilibria   Node: 256ccaf5bb62

Integer form of the matching-pennies payoffs.
-/

/-- Integer form of the matching-pennies payoffs. -/
def agMPv (p i : Fin 2) (y : Fin 2 → ℕ) : ℕ :=
  if p = 0 then (if y i = 1 then 1 else 0) else (if y i = 0 then 1 else 0)
