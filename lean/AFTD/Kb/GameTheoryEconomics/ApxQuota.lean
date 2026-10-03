import AFTD.Prelude

/-!
# apx_quota

Topic: social_choice   Node: 29c1df2237b7

Boolean natural-number test of quota for four states.
-/

/-- Boolean quota test (natural-number form) for four states. -/
def apx_quota (p : Fin 4 → ℕ) (h : ℕ) (a : Fin 4 → ℕ) : Bool :=
  decide (a 0 + a 1 + a 2 + a 3 = h) &&
  (List.finRange 4).all fun i =>
    decide (h * p i < (a i + 1) * (p 0 + p 1 + p 2 + p 3)) &&
    decide (a i * (p 0 + p 1 + p 2 + p 3) < h * p i + (p 0 + p 1 + p 2 + p 3))
